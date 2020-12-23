%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 155 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  299 ( 444 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f72,f76,f80,f84,f88,f112,f122,f126,f142,f148,f156,f191,f229,f270])).

fof(f270,plain,
    ( ~ spl3_5
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f71,f228,f111])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X0,X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f228,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_29
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f71,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f229,plain,
    ( spl3_29
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f210,f188,f153,f145,f120,f82,f226])).

fof(f82,plain,
    ( spl3_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f120,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X1),k2_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f145,plain,
    ( spl3_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f153,plain,
    ( spl3_20
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f188,plain,
    ( spl3_24
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f210,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f207,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f155,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f155,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f207,plain,
    ( r2_hidden(sK2(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(unit_resulting_resolution,[],[f147,f190,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X1),k2_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f190,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f188])).

fof(f147,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f191,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f149,f145,f139,f124,f60,f55,f50,f188])).

fof(f50,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( spl3_3
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( v5_funct_1(X1,X0)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f139,plain,
    ( spl3_18
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f149,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f52,f57,f62,f141,f147,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | v5_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f141,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f62,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f57,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f52,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f156,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f86,f65,f153])).

fof(f65,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( spl3_9
  <=> ! [X0] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f98,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f67,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f67,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f148,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f91,f78,f65,f145])).

fof(f78,plain,
    ( spl3_7
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f67,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f142,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f89,f74,f65,f139])).

fof(f74,plain,
    ( spl3_6
  <=> ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f89,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f67,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_funct_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f126,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f43,f124])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f122,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f46,f120])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f31])).

fof(f31,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK2(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f112,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f48,f110])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f88,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f84,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f80,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f76,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f72,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f58,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f55])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (29757)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.45  % (29768)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.45  % (29757)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f273,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f72,f76,f80,f84,f88,f112,f122,f126,f142,f148,f156,f191,f229,f270])).
% 0.22/0.45  fof(f270,plain,(
% 0.22/0.45    ~spl3_5 | ~spl3_12 | ~spl3_29),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.45  fof(f263,plain,(
% 0.22/0.45    $false | (~spl3_5 | ~spl3_12 | ~spl3_29)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f71,f228,f111])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) ) | ~spl3_12),
% 0.22/0.45    inference(avatar_component_clause,[],[f110])).
% 0.22/0.45  fof(f110,plain,(
% 0.22/0.45    spl3_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.45  fof(f228,plain,(
% 0.22/0.45    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl3_29),
% 0.22/0.45    inference(avatar_component_clause,[],[f226])).
% 0.22/0.45  fof(f226,plain,(
% 0.22/0.45    spl3_29 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f70])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    spl3_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f229,plain,(
% 0.22/0.45    spl3_29 | ~spl3_8 | ~spl3_14 | ~spl3_19 | ~spl3_20 | ~spl3_24),
% 0.22/0.45    inference(avatar_split_clause,[],[f210,f188,f153,f145,f120,f82,f226])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl3_8 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    spl3_14 <=> ! [X1,X0] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f145,plain,(
% 0.22/0.45    spl3_19 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.45  fof(f153,plain,(
% 0.22/0.45    spl3_20 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.45  fof(f188,plain,(
% 0.22/0.45    spl3_24 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.45  fof(f210,plain,(
% 0.22/0.45    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | (~spl3_8 | ~spl3_14 | ~spl3_19 | ~spl3_20 | ~spl3_24)),
% 0.22/0.45    inference(forward_demodulation,[],[f207,f159])).
% 0.22/0.45  fof(f159,plain,(
% 0.22/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_20)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f155,f83])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl3_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl3_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f153])).
% 0.22/0.45  fof(f207,plain,(
% 0.22/0.45    r2_hidden(sK2(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl3_14 | ~spl3_19 | ~spl3_24)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f147,f190,f121])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f120])).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl3_24),
% 0.22/0.45    inference(avatar_component_clause,[],[f188])).
% 0.22/0.45  fof(f147,plain,(
% 0.22/0.45    v1_relat_1(k1_xboole_0) | ~spl3_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f145])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    spl3_24 | ~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_15 | ~spl3_18 | ~spl3_19),
% 0.22/0.45    inference(avatar_split_clause,[],[f149,f145,f139,f124,f60,f55,f50,f188])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl3_1 <=> v1_relat_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl3_2 <=> v1_funct_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    spl3_3 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f124,plain,(
% 0.22/0.45    spl3_15 <=> ! [X1,X0] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    spl3_18 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_15 | ~spl3_18 | ~spl3_19)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f52,f57,f62,f141,f147,f125])).
% 0.22/0.45  fof(f125,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f124])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    v1_funct_1(k1_xboole_0) | ~spl3_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f139])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ~v5_funct_1(k1_xboole_0,sK0) | spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f60])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    v1_funct_1(sK0) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f55])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    v1_relat_1(sK0) | ~spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f50])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    spl3_20 | ~spl3_4 | ~spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f98,f86,f65,f153])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    spl3_9 <=> ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    v1_xboole_0(k2_relat_1(k1_xboole_0)) | (~spl3_4 | ~spl3_9)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f67,f87])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f86])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f65])).
% 0.22/0.45  fof(f148,plain,(
% 0.22/0.45    spl3_19 | ~spl3_4 | ~spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f91,f78,f65,f145])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl3_7 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    v1_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_7)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f67,f79])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl3_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f78])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    spl3_18 | ~spl3_4 | ~spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f89,f74,f65,f139])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    spl3_6 <=> ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    v1_funct_1(k1_xboole_0) | (~spl3_4 | ~spl3_6)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f67,f75])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) ) | ~spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f74])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    spl3_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f43,f124])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(rectify,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    spl3_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f46,f120])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK2(X1),k2_relat_1(X1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    spl3_12),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f110])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f41,f86])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl3_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f40,f82])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f39,f78])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl3_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f38,f74])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f37,f70])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl3_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    v1_xboole_0(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ~spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f35,f60])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.45    inference(negated_conjecture,[],[f12])).
% 0.22/0.45  fof(f12,conjecture,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f34,f55])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    v1_funct_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f50])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (29757)------------------------------
% 0.22/0.45  % (29757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (29757)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (29757)Memory used [KB]: 6268
% 0.22/0.45  % (29757)Time elapsed: 0.048 s
% 0.22/0.45  % (29757)------------------------------
% 0.22/0.45  % (29757)------------------------------
% 0.22/0.45  % (29751)Success in time 0.087 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 185 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :    7
%              Number of atoms          :  349 ( 935 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f60,f65,f69,f73,f77,f81,f108,f121,f139,f158,f206,f220,f248])).

fof(f248,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f246,f49])).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f246,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f245,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f245,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_35 ),
    inference(resolution,[],[f219,f39])).

fof(f39,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f219,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_35
  <=> ! [X1] :
        ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f220,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f216,f204,f71,f57,f52,f218])).

fof(f52,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f57,plain,
    ( spl4_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f204,plain,
    ( spl4_33
  <=> ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK1,sK2),X0)
        | r1_tarski(k5_relat_1(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f216,plain,
    ( ! [X1] :
        ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f215,f54])).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f215,plain,
    ( ! [X1] :
        ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f208,f59])).

fof(f59,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f208,plain,
    ( ! [X1] :
        ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_9
    | ~ spl4_33 ),
    inference(resolution,[],[f205,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK1,sK2),X0)
        | r1_tarski(k5_relat_1(sK0,sK2),X0) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl4_33
    | ~ spl4_11
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f202,f155,f79,f204])).

fof(f79,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f155,plain,
    ( spl4_25
  <=> k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK1,sK2),X0)
        | r1_tarski(k5_relat_1(sK0,sK2),X0) )
    | ~ spl4_11
    | ~ spl4_25 ),
    inference(superposition,[],[f80,f157])).

fof(f157,plain,
    ( k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f158,plain,
    ( spl4_25
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f142,f137,f52,f155])).

fof(f137,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f142,plain,
    ( k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(resolution,[],[f138,f54])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0)) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl4_22
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f135,f119,f57,f42,f137])).

fof(f42,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f119,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(sK0,X1)
        | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0)) )
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0)) )
    | ~ spl4_3
    | ~ spl4_18 ),
    inference(resolution,[],[f120,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f114,f106,f62,f119])).

fof(f62,plain,
    ( spl4_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( spl4_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(sK0,X1)
        | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0)) )
    | ~ spl4_7
    | ~ spl4_16 ),
    inference(resolution,[],[f107,f64])).

fof(f64,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1)
        | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl4_16
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f104,f75,f67,f106])).

fof(f67,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f75,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) )
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f81,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f77,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f73,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f69,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f60,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f32])).

fof(f26,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (9891)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (9888)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (9886)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (9888)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f249,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f60,f65,f69,f73,f77,f81,f108,f121,f139,f158,f206,f220,f248])).
% 0.21/0.43  fof(f248,plain,(
% 0.21/0.43    spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_35),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.43  fof(f247,plain,(
% 0.21/0.43    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_35)),
% 0.21/0.43    inference(subsumption_resolution,[],[f246,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f246,plain,(
% 0.21/0.43    ~v1_relat_1(sK3) | (spl4_1 | ~spl4_2 | ~spl4_35)),
% 0.21/0.43    inference(subsumption_resolution,[],[f245,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl4_1 <=> r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f245,plain,(
% 0.21/0.43    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) | ~v1_relat_1(sK3) | (~spl4_2 | ~spl4_35)),
% 0.21/0.43    inference(resolution,[],[f219,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f219,plain,(
% 0.21/0.43    ( ! [X1] : (~r1_tarski(sK2,X1) | r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1)) | ~v1_relat_1(X1)) ) | ~spl4_35),
% 0.21/0.43    inference(avatar_component_clause,[],[f218])).
% 0.21/0.43  fof(f218,plain,(
% 0.21/0.43    spl4_35 <=> ! [X1] : (r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.43  fof(f220,plain,(
% 0.21/0.43    spl4_35 | ~spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_33),
% 0.21/0.43    inference(avatar_split_clause,[],[f216,f204,f71,f57,f52,f218])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl4_5 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl4_6 <=> v1_relat_1(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f204,plain,(
% 0.21/0.43    spl4_33 <=> ! [X0] : (~r1_tarski(k5_relat_1(sK1,sK2),X0) | r1_tarski(k5_relat_1(sK0,sK2),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.43  fof(f216,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_33)),
% 0.21/0.43    inference(subsumption_resolution,[],[f215,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f52])).
% 0.21/0.43  fof(f215,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | (~spl4_6 | ~spl4_9 | ~spl4_33)),
% 0.21/0.43    inference(subsumption_resolution,[],[f208,f59])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    v1_relat_1(sK1) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f208,plain,(
% 0.21/0.43    ( ! [X1] : (r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(sK1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | (~spl4_9 | ~spl4_33)),
% 0.21/0.43    inference(resolution,[],[f205,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f205,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k5_relat_1(sK1,sK2),X0) | r1_tarski(k5_relat_1(sK0,sK2),X0)) ) | ~spl4_33),
% 0.21/0.43    inference(avatar_component_clause,[],[f204])).
% 0.21/0.43  fof(f206,plain,(
% 0.21/0.43    spl4_33 | ~spl4_11 | ~spl4_25),
% 0.21/0.43    inference(avatar_split_clause,[],[f202,f155,f79,f204])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl4_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    spl4_25 <=> k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.43  fof(f202,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k5_relat_1(sK1,sK2),X0) | r1_tarski(k5_relat_1(sK0,sK2),X0)) ) | (~spl4_11 | ~spl4_25)),
% 0.21/0.43    inference(superposition,[],[f80,f157])).
% 0.21/0.43  fof(f157,plain,(
% 0.21/0.43    k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) | ~spl4_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f155])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f79])).
% 0.21/0.43  fof(f158,plain,(
% 0.21/0.43    spl4_25 | ~spl4_5 | ~spl4_22),
% 0.21/0.43    inference(avatar_split_clause,[],[f142,f137,f52,f155])).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    spl4_22 <=> ! [X0] : (~v1_relat_1(X0) | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.43  fof(f142,plain,(
% 0.21/0.43    k5_relat_1(sK1,sK2) = k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) | (~spl4_5 | ~spl4_22)),
% 0.21/0.43    inference(resolution,[],[f138,f54])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0))) ) | ~spl4_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f137])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    spl4_22 | ~spl4_3 | ~spl4_6 | ~spl4_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f135,f119,f57,f42,f137])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl4_18 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_6 | ~spl4_18)),
% 0.21/0.43    inference(subsumption_resolution,[],[f134,f59])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | k5_relat_1(sK1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_18)),
% 0.21/0.43    inference(resolution,[],[f120,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0))) ) | ~spl4_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f119])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    spl4_18 | ~spl4_7 | ~spl4_16),
% 0.21/0.43    inference(avatar_split_clause,[],[f114,f106,f62,f119])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl4_7 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    spl4_16 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | k5_relat_1(X1,X0) = k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(X1,X0))) ) | (~spl4_7 | ~spl4_16)),
% 0.21/0.43    inference(resolution,[],[f107,f64])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl4_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2))) ) | ~spl4_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f106])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    spl4_16 | ~spl4_8 | ~spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f104,f75,f67,f106])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl4_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X2) = k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X1,X2))) ) | (~spl4_8 | ~spl4_10)),
% 0.21/0.43    inference(resolution,[],[f68,f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f75])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f79])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl4_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f75])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl4_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl4_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl4_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f62])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    (((~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) => (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl4_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f57])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl4_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f52])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v1_relat_1(sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f47])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    v1_relat_1(sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f42])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f25,f37])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    r1_tarski(sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~spl4_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f32])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9888)------------------------------
% 0.21/0.44  % (9888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9888)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9888)Memory used [KB]: 10618
% 0.21/0.44  % (9888)Time elapsed: 0.011 s
% 0.21/0.44  % (9888)------------------------------
% 0.21/0.44  % (9888)------------------------------
% 0.21/0.44  % (9889)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (9875)Success in time 0.081 s
%------------------------------------------------------------------------------

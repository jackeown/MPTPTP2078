%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:25 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 254 expanded)
%              Number of leaves         :   31 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  427 (1053 expanded)
%              Number of equality atoms :   55 ( 146 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f132,f137,f146,f225,f230,f300,f352,f594])).

fof(f594,plain,
    ( ~ spl4_4
    | spl4_14
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl4_4
    | spl4_14
    | spl4_20 ),
    inference(subsumption_resolution,[],[f592,f229])).

fof(f229,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_14
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f592,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl4_4
    | spl4_20 ),
    inference(backward_demodulation,[],[f399,f586])).

fof(f586,plain,
    ( k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0))
    | ~ spl4_4
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f351,f335])).

fof(f335,plain,
    ( ! [X8,X9] :
        ( r1_xboole_0(X9,k1_tarski(X8))
        | sK3(X9,k1_tarski(X8)) = X8 )
    | ~ spl4_4 ),
    inference(resolution,[],[f207,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f207,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k1_tarski(X3))
        | X3 = X4 )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f202,f126])).

fof(f126,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f109,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f109,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f202,plain,(
    ! [X4,X3] :
      ( r2_hidden(X4,k1_xboole_0)
      | X3 = X4
      | ~ r2_hidden(X4,k1_tarski(X3)) ) ),
    inference(superposition,[],[f80,f161])).

fof(f161,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f351,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl4_20
  <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f399,plain,
    ( r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),sK1)
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f351,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f352,plain,
    ( ~ spl4_20
    | spl4_19 ),
    inference(avatar_split_clause,[],[f309,f297,f349])).

fof(f297,plain,
    ( spl4_19
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f309,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f299,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f299,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f297])).

fof(f300,plain,
    ( ~ spl4_19
    | spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f231,f222,f134,f297])).

fof(f134,plain,
    ( spl4_9
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f222,plain,
    ( spl4_13
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f231,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_9
    | ~ spl4_13 ),
    inference(superposition,[],[f136,f224])).

fof(f224,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f136,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f230,plain,
    ( ~ spl4_14
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_10 ),
    inference(avatar_split_clause,[],[f189,f143,f129,f122,f117,f112,f107,f102,f227])).

fof(f102,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( spl4_5
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f117,plain,
    ( spl4_6
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f122,plain,
    ( spl4_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f129,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,
    ( spl4_10
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f189,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f109,f104,f145,f119,f114,f124,f131,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f58,f58,f58,f58])).

fof(f58,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f124,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f114,plain,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f119,plain,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f145,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f225,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f195,f129,f117,f112,f102,f97,f92,f222])).

fof(f92,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f97,plain,
    ( spl4_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f195,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f193,f179])).

fof(f179,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f131,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f193,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f94,f99,f104,f119,f114,f131,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f58,f58,f58,f58])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f99,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f94,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f146,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f141,f97,f92,f143])).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f94,f99,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f137,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f54,f134])).

fof(f54,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f132,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f82,f129])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f53,f58])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f85,f122])).

fof(f85,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f50,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f84,f117])).

fof(f84,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f51,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f115,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f83,f112])).

fof(f83,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f52,f58])).

fof(f52,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f105,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f47,f92])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:06:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (15323)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (15302)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.49  % (15323)Refutation not found, incomplete strategy% (15323)------------------------------
% 0.22/0.49  % (15323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15323)Memory used [KB]: 1663
% 0.22/0.49  % (15323)Time elapsed: 0.067 s
% 0.22/0.49  % (15323)------------------------------
% 0.22/0.49  % (15323)------------------------------
% 0.22/0.51  % (15297)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (15296)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (15298)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (15295)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (15320)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (15301)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (15316)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (15312)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (15294)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (15299)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (15305)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (15315)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (15318)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (15295)Refutation not found, incomplete strategy% (15295)------------------------------
% 0.22/0.53  % (15295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15295)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15295)Memory used [KB]: 1791
% 0.22/0.53  % (15295)Time elapsed: 0.098 s
% 0.22/0.53  % (15295)------------------------------
% 0.22/0.53  % (15295)------------------------------
% 0.22/0.54  % (15306)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (15310)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (15310)Refutation not found, incomplete strategy% (15310)------------------------------
% 0.22/0.54  % (15310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15310)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15310)Memory used [KB]: 10618
% 0.22/0.54  % (15310)Time elapsed: 0.130 s
% 0.22/0.54  % (15310)------------------------------
% 0.22/0.54  % (15310)------------------------------
% 0.22/0.54  % (15322)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (15308)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (15319)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (15322)Refutation not found, incomplete strategy% (15322)------------------------------
% 0.22/0.54  % (15322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15322)Memory used [KB]: 10746
% 0.22/0.54  % (15322)Time elapsed: 0.130 s
% 0.22/0.54  % (15322)------------------------------
% 0.22/0.54  % (15322)------------------------------
% 1.39/0.54  % (15308)Refutation not found, incomplete strategy% (15308)------------------------------
% 1.39/0.54  % (15308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (15309)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.54  % (15321)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (15320)Refutation not found, incomplete strategy% (15320)------------------------------
% 1.39/0.55  % (15320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (15320)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (15320)Memory used [KB]: 6268
% 1.39/0.55  % (15320)Time elapsed: 0.133 s
% 1.39/0.55  % (15320)------------------------------
% 1.39/0.55  % (15320)------------------------------
% 1.39/0.55  % (15308)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (15308)Memory used [KB]: 1791
% 1.39/0.55  % (15308)Time elapsed: 0.101 s
% 1.39/0.55  % (15308)------------------------------
% 1.39/0.55  % (15308)------------------------------
% 1.39/0.55  % (15314)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (15300)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (15307)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (15303)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (15311)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.55  % (15311)Refutation not found, incomplete strategy% (15311)------------------------------
% 1.39/0.55  % (15311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (15311)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (15311)Memory used [KB]: 1791
% 1.39/0.55  % (15311)Time elapsed: 0.140 s
% 1.39/0.55  % (15311)------------------------------
% 1.39/0.55  % (15311)------------------------------
% 1.39/0.55  % (15313)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (15304)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (15304)Refutation not found, incomplete strategy% (15304)------------------------------
% 1.39/0.55  % (15304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (15304)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (15304)Memory used [KB]: 10746
% 1.39/0.55  % (15304)Time elapsed: 0.142 s
% 1.39/0.55  % (15304)------------------------------
% 1.39/0.55  % (15304)------------------------------
% 1.39/0.56  % (15317)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.58  % (15314)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f595,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f132,f137,f146,f225,f230,f300,f352,f594])).
% 1.60/0.58  fof(f594,plain,(
% 1.60/0.58    ~spl4_4 | spl4_14 | spl4_20),
% 1.60/0.58    inference(avatar_contradiction_clause,[],[f593])).
% 1.60/0.58  fof(f593,plain,(
% 1.60/0.58    $false | (~spl4_4 | spl4_14 | spl4_20)),
% 1.60/0.58    inference(subsumption_resolution,[],[f592,f229])).
% 1.60/0.58  fof(f229,plain,(
% 1.60/0.58    ~r2_hidden(k1_xboole_0,sK1) | spl4_14),
% 1.60/0.58    inference(avatar_component_clause,[],[f227])).
% 1.60/0.58  fof(f227,plain,(
% 1.60/0.58    spl4_14 <=> r2_hidden(k1_xboole_0,sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.60/0.58  fof(f592,plain,(
% 1.60/0.58    r2_hidden(k1_xboole_0,sK1) | (~spl4_4 | spl4_20)),
% 1.60/0.58    inference(backward_demodulation,[],[f399,f586])).
% 1.60/0.58  fof(f586,plain,(
% 1.60/0.58    k1_xboole_0 = sK3(sK1,k1_tarski(k1_xboole_0)) | (~spl4_4 | spl4_20)),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f351,f335])).
% 1.60/0.58  fof(f335,plain,(
% 1.60/0.58    ( ! [X8,X9] : (r1_xboole_0(X9,k1_tarski(X8)) | sK3(X9,k1_tarski(X8)) = X8) ) | ~spl4_4),
% 1.60/0.58    inference(resolution,[],[f207,f67])).
% 1.60/0.58  fof(f67,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f39])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(rectify,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.60/0.58  fof(f207,plain,(
% 1.60/0.58    ( ! [X4,X3] : (~r2_hidden(X4,k1_tarski(X3)) | X3 = X4) ) | ~spl4_4),
% 1.60/0.58    inference(subsumption_resolution,[],[f202,f126])).
% 1.60/0.58  fof(f126,plain,(
% 1.60/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_4),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f109,f62])).
% 1.60/0.58  fof(f62,plain,(
% 1.60/0.58    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.60/0.58    inference(rectify,[],[f35])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.60/0.58    inference(nnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.60/0.58  fof(f109,plain,(
% 1.60/0.58    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 1.60/0.58    inference(avatar_component_clause,[],[f107])).
% 1.60/0.58  fof(f107,plain,(
% 1.60/0.58    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.60/0.58  fof(f202,plain,(
% 1.60/0.58    ( ! [X4,X3] : (r2_hidden(X4,k1_xboole_0) | X3 = X4 | ~r2_hidden(X4,k1_tarski(X3))) )),
% 1.60/0.58    inference(superposition,[],[f80,f161])).
% 1.60/0.58  fof(f161,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f88,f75])).
% 1.60/0.58  fof(f75,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.60/0.58    inference(nnf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.60/0.58  fof(f88,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.58    inference(equality_resolution,[],[f70])).
% 1.60/0.58  fof(f70,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.58    inference(cnf_transformation,[],[f42])).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(flattening,[],[f41])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(nnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.58  fof(f80,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f46])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.60/0.58    inference(flattening,[],[f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.60/0.58    inference(nnf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.60/0.58  fof(f351,plain,(
% 1.60/0.58    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_20),
% 1.60/0.58    inference(avatar_component_clause,[],[f349])).
% 1.60/0.58  fof(f349,plain,(
% 1.60/0.58    spl4_20 <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.60/0.58  fof(f399,plain,(
% 1.60/0.58    r2_hidden(sK3(sK1,k1_tarski(k1_xboole_0)),sK1) | spl4_20),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f351,f66])).
% 1.60/0.58  fof(f66,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f40])).
% 1.60/0.58  fof(f352,plain,(
% 1.60/0.58    ~spl4_20 | spl4_19),
% 1.60/0.58    inference(avatar_split_clause,[],[f309,f297,f349])).
% 1.60/0.58  fof(f297,plain,(
% 1.60/0.58    spl4_19 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.60/0.58  fof(f309,plain,(
% 1.60/0.58    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_19),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f299,f72])).
% 1.60/0.58  fof(f72,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f43])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.60/0.58    inference(nnf_transformation,[],[f10])).
% 1.60/0.58  fof(f10,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.60/0.58  fof(f299,plain,(
% 1.60/0.58    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl4_19),
% 1.60/0.58    inference(avatar_component_clause,[],[f297])).
% 1.60/0.58  fof(f300,plain,(
% 1.60/0.58    ~spl4_19 | spl4_9 | ~spl4_13),
% 1.60/0.58    inference(avatar_split_clause,[],[f231,f222,f134,f297])).
% 1.60/0.58  fof(f134,plain,(
% 1.60/0.58    spl4_9 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.60/0.58  fof(f222,plain,(
% 1.60/0.58    spl4_13 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.60/0.58  fof(f231,plain,(
% 1.60/0.58    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl4_9 | ~spl4_13)),
% 1.60/0.58    inference(superposition,[],[f136,f224])).
% 1.60/0.58  fof(f224,plain,(
% 1.60/0.58    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl4_13),
% 1.60/0.58    inference(avatar_component_clause,[],[f222])).
% 1.60/0.58  fof(f136,plain,(
% 1.60/0.58    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl4_9),
% 1.60/0.58    inference(avatar_component_clause,[],[f134])).
% 1.60/0.58  fof(f230,plain,(
% 1.60/0.58    ~spl4_14 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_10),
% 1.60/0.58    inference(avatar_split_clause,[],[f189,f143,f129,f122,f117,f112,f107,f102,f227])).
% 1.60/0.58  fof(f102,plain,(
% 1.60/0.58    spl4_3 <=> v1_xboole_0(sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.60/0.58  fof(f112,plain,(
% 1.60/0.58    spl4_5 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.60/0.58  fof(f117,plain,(
% 1.60/0.58    spl4_6 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.60/0.58  fof(f122,plain,(
% 1.60/0.58    spl4_7 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.60/0.58  fof(f129,plain,(
% 1.60/0.58    spl4_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.60/0.58  fof(f143,plain,(
% 1.60/0.58    spl4_10 <=> v1_xboole_0(k2_struct_0(sK0))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.60/0.58  fof(f189,plain,(
% 1.60/0.58    ~r2_hidden(k1_xboole_0,sK1) | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_10)),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f109,f104,f145,f119,f114,f124,f131,f86])).
% 1.60/0.58  fof(f86,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f59,f58,f58,f58,f58])).
% 1.60/0.58  fof(f58,plain,(
% 1.60/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.60/0.58  fof(f15,axiom,(
% 1.60/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.60/0.58  fof(f59,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f24])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.60/0.58    inference(flattening,[],[f23])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,axiom,(
% 1.60/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 1.60/0.58  fof(f131,plain,(
% 1.60/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl4_8),
% 1.60/0.58    inference(avatar_component_clause,[],[f129])).
% 1.60/0.58  fof(f124,plain,(
% 1.60/0.58    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~spl4_7),
% 1.60/0.58    inference(avatar_component_clause,[],[f122])).
% 1.60/0.58  fof(f114,plain,(
% 1.60/0.58    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl4_5),
% 1.60/0.58    inference(avatar_component_clause,[],[f112])).
% 1.60/0.58  fof(f119,plain,(
% 1.60/0.58    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl4_6),
% 1.60/0.58    inference(avatar_component_clause,[],[f117])).
% 1.60/0.58  fof(f145,plain,(
% 1.60/0.58    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_10),
% 1.60/0.58    inference(avatar_component_clause,[],[f143])).
% 1.60/0.58  fof(f104,plain,(
% 1.60/0.58    ~v1_xboole_0(sK1) | spl4_3),
% 1.60/0.58    inference(avatar_component_clause,[],[f102])).
% 1.60/0.58  fof(f225,plain,(
% 1.60/0.58    spl4_13 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_8),
% 1.60/0.58    inference(avatar_split_clause,[],[f195,f129,f117,f112,f102,f97,f92,f222])).
% 1.60/0.58  fof(f92,plain,(
% 1.60/0.58    spl4_1 <=> v2_struct_0(sK0)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.60/0.58  fof(f97,plain,(
% 1.60/0.58    spl4_2 <=> l1_struct_0(sK0)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.60/0.58  fof(f195,plain,(
% 1.60/0.58    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 1.60/0.58    inference(forward_demodulation,[],[f193,f179])).
% 1.60/0.58  fof(f179,plain,(
% 1.60/0.58    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl4_8),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f131,f77])).
% 1.60/0.58  fof(f77,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f31])).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f13])).
% 1.60/0.58  fof(f13,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.60/0.58  fof(f193,plain,(
% 1.60/0.58    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_8)),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f94,f99,f104,f119,f114,f131,f87])).
% 1.60/0.58  fof(f87,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | v2_struct_0(X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f61,f58,f58,f58,f58])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f27])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,axiom,(
% 1.60/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 1.60/0.58  fof(f99,plain,(
% 1.60/0.58    l1_struct_0(sK0) | ~spl4_2),
% 1.60/0.58    inference(avatar_component_clause,[],[f97])).
% 1.60/0.58  fof(f94,plain,(
% 1.60/0.58    ~v2_struct_0(sK0) | spl4_1),
% 1.60/0.58    inference(avatar_component_clause,[],[f92])).
% 1.60/0.58  fof(f146,plain,(
% 1.60/0.58    ~spl4_10 | spl4_1 | ~spl4_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f141,f97,f92,f143])).
% 1.60/0.58  fof(f141,plain,(
% 1.60/0.58    ~v1_xboole_0(k2_struct_0(sK0)) | (spl4_1 | ~spl4_2)),
% 1.60/0.58    inference(unit_resulting_resolution,[],[f94,f99,f60])).
% 1.60/0.58  fof(f60,plain,(
% 1.60/0.58    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,axiom,(
% 1.60/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.60/0.58  fof(f137,plain,(
% 1.60/0.58    ~spl4_9),
% 1.60/0.58    inference(avatar_split_clause,[],[f54,f134])).
% 1.60/0.58  fof(f54,plain,(
% 1.60/0.58    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f33,f32])).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.60/0.58    inference(flattening,[],[f21])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,negated_conjecture,(
% 1.60/0.58    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.60/0.58    inference(negated_conjecture,[],[f18])).
% 1.60/0.58  fof(f18,conjecture,(
% 1.60/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 1.60/0.58  fof(f132,plain,(
% 1.60/0.58    spl4_8),
% 1.60/0.58    inference(avatar_split_clause,[],[f82,f129])).
% 1.60/0.58  fof(f82,plain,(
% 1.60/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.60/0.58    inference(definition_unfolding,[],[f53,f58])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f125,plain,(
% 1.60/0.58    spl4_7),
% 1.60/0.58    inference(avatar_split_clause,[],[f85,f122])).
% 1.60/0.58  fof(f85,plain,(
% 1.60/0.58    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.60/0.58    inference(definition_unfolding,[],[f50,f58])).
% 1.60/0.58  fof(f50,plain,(
% 1.60/0.58    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f120,plain,(
% 1.60/0.58    spl4_6),
% 1.60/0.58    inference(avatar_split_clause,[],[f84,f117])).
% 1.60/0.58  fof(f84,plain,(
% 1.60/0.58    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.60/0.58    inference(definition_unfolding,[],[f51,f58])).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f115,plain,(
% 1.60/0.58    spl4_5),
% 1.60/0.58    inference(avatar_split_clause,[],[f83,f112])).
% 1.60/0.58  fof(f83,plain,(
% 1.60/0.58    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.60/0.58    inference(definition_unfolding,[],[f52,f58])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f110,plain,(
% 1.60/0.58    spl4_4),
% 1.60/0.58    inference(avatar_split_clause,[],[f55,f107])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    v1_xboole_0(k1_xboole_0)),
% 1.60/0.58    inference(cnf_transformation,[],[f2])).
% 1.60/0.58  fof(f2,axiom,(
% 1.60/0.58    v1_xboole_0(k1_xboole_0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.60/0.58  fof(f105,plain,(
% 1.60/0.58    ~spl4_3),
% 1.60/0.58    inference(avatar_split_clause,[],[f49,f102])).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    ~v1_xboole_0(sK1)),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f100,plain,(
% 1.60/0.58    spl4_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f48,f97])).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    l1_struct_0(sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  fof(f95,plain,(
% 1.60/0.58    ~spl4_1),
% 1.60/0.58    inference(avatar_split_clause,[],[f47,f92])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ~v2_struct_0(sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f34])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (15314)------------------------------
% 1.60/0.58  % (15314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (15314)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (15314)Memory used [KB]: 11129
% 1.60/0.58  % (15314)Time elapsed: 0.172 s
% 1.60/0.58  % (15314)------------------------------
% 1.60/0.58  % (15314)------------------------------
% 1.60/0.58  % (15293)Success in time 0.212 s
%------------------------------------------------------------------------------

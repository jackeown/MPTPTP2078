%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t32_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:13 EDT 2019

% Result     : Theorem 11.65s
% Output     : Refutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  285 ( 735 expanded)
%              Number of leaves         :   65 ( 314 expanded)
%              Depth                    :   14
%              Number of atoms          : 1339 (4572 expanded)
%              Number of equality atoms :   71 ( 134 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f172,f179,f186,f193,f200,f228,f235,f242,f249,f281,f293,f315,f324,f380,f744,f750,f758,f797,f1772,f2236,f2855,f2882,f3743,f6004,f6064,f6071,f7852,f13949,f22814,f32786,f48843,f57889,f96677,f157708,f161678,f170525,f213292,f221598,f228527,f228702,f228703])).

fof(f228703,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) != u1_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) != k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2)))
    | ~ r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK2,sK3))) ),
    introduced(theory_axiom,[])).

fof(f228702,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | spl10_107
    | ~ spl10_3014
    | ~ spl10_6984
    | ~ spl10_9188 ),
    inference(avatar_contradiction_clause,[],[f228701])).

fof(f228701,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_107
    | ~ spl10_3014
    | ~ spl10_6984
    | ~ spl10_9188 ),
    inference(unit_resulting_resolution,[],[f171,f178,f57869,f157691,f215504,f796,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t4_tsep_1)).

fof(f796,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl10_107 ),
    inference(avatar_component_clause,[],[f795])).

fof(f795,plain,
    ( spl10_107
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_107])])).

fof(f215504,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2)))
    | ~ spl10_9188 ),
    inference(avatar_component_clause,[],[f215503])).

fof(f215503,plain,
    ( spl10_9188
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9188])])).

fof(f157691,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ spl10_6984 ),
    inference(avatar_component_clause,[],[f157690])).

fof(f157690,plain,
    ( spl10_6984
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6984])])).

fof(f57869,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl10_3014 ),
    inference(avatar_component_clause,[],[f57868])).

fof(f57868,plain,
    ( spl10_3014
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3014])])).

fof(f178,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl10_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f171,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f228527,plain,
    ( spl10_7026
    | ~ spl10_264
    | ~ spl10_1470
    | ~ spl10_4730 ),
    inference(avatar_split_clause,[],[f221782,f96675,f23367,f2228,f164453])).

fof(f164453,plain,
    ( spl10_7026
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7026])])).

fof(f2228,plain,
    ( spl10_264
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f23367,plain,
    ( spl10_1470
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1470])])).

fof(f96675,plain,
    ( spl10_4730
  <=> ! [X30] : r1_tarski(k3_xboole_0(u1_struct_0(sK2),X30),k3_xboole_0(u1_struct_0(sK3),X30)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4730])])).

fof(f221782,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3)))
    | ~ spl10_264
    | ~ spl10_1470
    | ~ spl10_4730 ),
    inference(forward_demodulation,[],[f221781,f2229])).

fof(f2229,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_264 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f221781,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)))
    | ~ spl10_1470
    | ~ spl10_4730 ),
    inference(forward_demodulation,[],[f221639,f129])).

fof(f129,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',commutativity_k3_xboole_0)).

fof(f221639,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)))
    | ~ spl10_1470
    | ~ spl10_4730 ),
    inference(superposition,[],[f96676,f23368])).

fof(f23368,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl10_1470 ),
    inference(avatar_component_clause,[],[f23367])).

fof(f96676,plain,
    ( ! [X30] : r1_tarski(k3_xboole_0(u1_struct_0(sK2),X30),k3_xboole_0(u1_struct_0(sK3),X30))
    | ~ spl10_4730 ),
    inference(avatar_component_clause,[],[f96675])).

fof(f221598,plain,
    ( ~ spl10_210
    | spl10_1471 ),
    inference(avatar_contradiction_clause,[],[f221597])).

fof(f221597,plain,
    ( $false
    | ~ spl10_210
    | ~ spl10_1471 ),
    inference(subsumption_resolution,[],[f221594,f1771])).

fof(f1771,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_210 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f1770,plain,
    ( spl10_210
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f221594,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_1471 ),
    inference(superposition,[],[f23365,f129])).

fof(f23365,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl10_1471 ),
    inference(avatar_component_clause,[],[f23364])).

fof(f23364,plain,
    ( spl10_1471
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) != k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1471])])).

fof(f213292,plain,
    ( ~ spl10_2
    | ~ spl10_4
    | spl10_53
    | ~ spl10_2602
    | ~ spl10_3014
    | ~ spl10_7026 ),
    inference(avatar_contradiction_clause,[],[f213291])).

fof(f213291,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_53
    | ~ spl10_2602
    | ~ spl10_3014
    | ~ spl10_7026 ),
    inference(unit_resulting_resolution,[],[f171,f178,f57869,f48829,f164454,f379,f125])).

fof(f379,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl10_53
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f164454,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK1,sK3)))
    | ~ spl10_7026 ),
    inference(avatar_component_clause,[],[f164453])).

fof(f48829,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl10_2602 ),
    inference(avatar_component_clause,[],[f48828])).

fof(f48828,plain,
    ( spl10_2602
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2602])])).

fof(f170525,plain,
    ( spl10_7482
    | ~ spl10_210
    | ~ spl10_434
    | ~ spl10_630 ),
    inference(avatar_split_clause,[],[f163923,f5996,f3741,f1770,f170523])).

fof(f170523,plain,
    ( spl10_7482
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7482])])).

fof(f3741,plain,
    ( spl10_434
  <=> ! [X9] : r1_tarski(k3_xboole_0(u1_struct_0(sK1),X9),k3_xboole_0(u1_struct_0(sK3),X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_434])])).

fof(f5996,plain,
    ( spl10_630
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_630])])).

fof(f163923,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK2,sK3)))
    | ~ spl10_210
    | ~ spl10_434
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f163922,f5997])).

fof(f5997,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_630 ),
    inference(avatar_component_clause,[],[f5996])).

fof(f163922,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_210
    | ~ spl10_434 ),
    inference(forward_demodulation,[],[f163909,f129])).

fof(f163909,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)))
    | ~ spl10_210
    | ~ spl10_434 ),
    inference(superposition,[],[f3742,f1771])).

fof(f3742,plain,
    ( ! [X9] : r1_tarski(k3_xboole_0(u1_struct_0(sK1),X9),k3_xboole_0(u1_struct_0(sK3),X9))
    | ~ spl10_434 ),
    inference(avatar_component_clause,[],[f3741])).

fof(f161678,plain,
    ( ~ spl10_107
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f161175,f375,f795])).

fof(f375,plain,
    ( spl10_52
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f161175,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl10_52 ),
    inference(subsumption_resolution,[],[f109,f376])).

fof(f376,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f375])).

fof(f109,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
        & m1_pre_topc(sK2,sK3) )
      | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f83,f82,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                        & m1_pre_topc(X2,X3) )
                      | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,sK1,X3))
                    & m1_pre_topc(X2,X3) )
                  | ( ~ m1_pre_topc(k2_tsep_1(X0,sK1,X2),k2_tsep_1(X0,X3,X2))
                    & m1_pre_topc(sK1,X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                  & m1_pre_topc(X2,X3) )
                | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                  & m1_pre_topc(X1,X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X1,X3))
                & m1_pre_topc(sK2,X3) )
              | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,sK2),k2_tsep_1(X0,X3,sK2))
                & m1_pre_topc(X1,X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
              & m1_pre_topc(X2,X3) )
            | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
              & m1_pre_topc(X1,X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,sK3))
            & m1_pre_topc(X2,sK3) )
          | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,sK3,X2))
            & m1_pre_topc(X1,sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t32_tmap_1)).

fof(f157708,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_9
    | spl10_11
    | ~ spl10_20
    | ~ spl10_22
    | spl10_6985 ),
    inference(avatar_contradiction_clause,[],[f157707])).

fof(f157707,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157706,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f157706,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157705,f178])).

fof(f157705,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157704,f199])).

fof(f199,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_11
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f157704,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157703,f241])).

fof(f241,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl10_22
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f157703,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157702,f192])).

fof(f192,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl10_9
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f157702,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_6985 ),
    inference(subsumption_resolution,[],[f157700,f234])).

fof(f234,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl10_20
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f157700,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6985 ),
    inference(resolution,[],[f157694,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',dt_k2_tsep_1)).

fof(f157694,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ spl10_6985 ),
    inference(avatar_component_clause,[],[f157693])).

fof(f157693,plain,
    ( spl10_6985
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6985])])).

fof(f96677,plain,
    ( spl10_4730
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f92772,f322,f279,f96675])).

fof(f279,plain,
    ( spl10_34
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f322,plain,
    ( spl10_42
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f92772,plain,
    ( ! [X30] : r1_tarski(k3_xboole_0(u1_struct_0(sK2),X30),k3_xboole_0(u1_struct_0(sK3),X30))
    | ~ spl10_34
    | ~ spl10_42 ),
    inference(subsumption_resolution,[],[f92711,f323])).

fof(f323,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f92711,plain,
    ( ! [X30] :
        ( ~ l1_pre_topc(sK3)
        | r1_tarski(k3_xboole_0(u1_struct_0(sK2),X30),k3_xboole_0(u1_struct_0(sK3),X30)) )
    | ~ spl10_34 ),
    inference(resolution,[],[f280,f557])).

fof(f557,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_pre_topc(X4,X3)
      | ~ l1_pre_topc(X3)
      | r1_tarski(k3_xboole_0(u1_struct_0(X4),X5),k3_xboole_0(u1_struct_0(X3),X5)) ) ),
    inference(resolution,[],[f357,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t26_xboole_1)).

fof(f357,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f117,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t3_subset)).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t1_tsep_1)).

fof(f280,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f279])).

fof(f57889,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | spl10_3015 ),
    inference(avatar_contradiction_clause,[],[f57888])).

fof(f57888,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57887,f164])).

fof(f57887,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57886,f178])).

fof(f57886,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57885,f185])).

fof(f185,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl10_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f57885,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57884,f227])).

fof(f227,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl10_18
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f57884,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57883,f192])).

fof(f57883,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_3015 ),
    inference(subsumption_resolution,[],[f57881,f234])).

fof(f57881,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3015 ),
    inference(resolution,[],[f57872,f149])).

fof(f57872,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl10_3015 ),
    inference(avatar_component_clause,[],[f57871])).

fof(f57871,plain,
    ( spl10_3015
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3015])])).

fof(f48843,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_7
    | spl10_11
    | ~ spl10_18
    | ~ spl10_22
    | spl10_2603 ),
    inference(avatar_contradiction_clause,[],[f48842])).

fof(f48842,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48841,f164])).

fof(f48841,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48840,f178])).

fof(f48840,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_7
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48839,f185])).

fof(f48839,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48838,f227])).

fof(f48838,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_11
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48837,f199])).

fof(f48837,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_22
    | ~ spl10_2603 ),
    inference(subsumption_resolution,[],[f48835,f241])).

fof(f48835,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2603 ),
    inference(resolution,[],[f48832,f149])).

fof(f48832,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl10_2603 ),
    inference(avatar_component_clause,[],[f48831])).

fof(f48831,plain,
    ( spl10_2603
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2603])])).

fof(f32786,plain,
    ( spl10_338
    | ~ spl10_96
    | ~ spl10_336 ),
    inference(avatar_split_clause,[],[f32667,f2842,f748,f2848])).

fof(f2848,plain,
    ( spl10_338
  <=> ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | ~ l1_struct_0(X12)
        | r1_tsep_1(X12,sK2)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X12)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X12))
        | v2_struct_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_338])])).

fof(f748,plain,
    ( spl10_96
  <=> ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f2842,plain,
    ( spl10_336
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_336])])).

fof(f32667,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X12)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X12))
        | r1_tsep_1(X12,sK2)
        | ~ l1_struct_0(X12) )
    | ~ spl10_96
    | ~ spl10_336 ),
    inference(subsumption_resolution,[],[f32654,f2843])).

fof(f2843,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_336 ),
    inference(avatar_component_clause,[],[f2842])).

fof(f32654,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X12)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X12))
        | r1_tsep_1(X12,sK2)
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(sK2) )
    | ~ spl10_96 ),
    inference(resolution,[],[f749,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',symmetry_r1_tsep_1)).

fof(f749,plain,
    ( ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) )
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f748])).

fof(f22814,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | spl10_25
    | ~ spl10_34
    | ~ spl10_266 ),
    inference(avatar_contradiction_clause,[],[f22779])).

fof(f22779,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_25
    | ~ spl10_34
    | ~ spl10_266 ),
    inference(unit_resulting_resolution,[],[f164,f171,f178,f192,f185,f199,f234,f241,f227,f2235,f248,f280,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',t23_tmap_1)).

fof(f248,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl10_25
  <=> ~ r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f2235,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl10_266 ),
    inference(avatar_component_clause,[],[f2234])).

fof(f2234,plain,
    ( spl10_266
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f13949,plain,
    ( spl10_346
    | ~ spl10_100
    | ~ spl10_344 ),
    inference(avatar_split_clause,[],[f13559,f2869,f756,f2875])).

fof(f2875,plain,
    ( spl10_346
  <=> ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | ~ l1_struct_0(X12)
        | r1_tsep_1(X12,sK3)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X12)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X12))
        | v2_struct_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_346])])).

fof(f756,plain,
    ( spl10_100
  <=> ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f2869,plain,
    ( spl10_344
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_344])])).

fof(f13559,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X12)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X12))
        | r1_tsep_1(X12,sK3)
        | ~ l1_struct_0(X12) )
    | ~ spl10_100
    | ~ spl10_344 ),
    inference(subsumption_resolution,[],[f13550,f2870])).

fof(f2870,plain,
    ( l1_struct_0(sK3)
    | ~ spl10_344 ),
    inference(avatar_component_clause,[],[f2869])).

fof(f13550,plain,
    ( ! [X12] :
        ( ~ m1_pre_topc(X12,sK0)
        | v2_struct_0(X12)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X12)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X12))
        | r1_tsep_1(X12,sK3)
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(sK3) )
    | ~ spl10_100 ),
    inference(resolution,[],[f757,f137])).

fof(f757,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f756])).

fof(f7852,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | spl10_25
    | ~ spl10_32
    | ~ spl10_632 ),
    inference(avatar_contradiction_clause,[],[f7846])).

fof(f7846,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_25
    | ~ spl10_32
    | ~ spl10_632 ),
    inference(unit_resulting_resolution,[],[f164,f171,f178,f185,f192,f199,f227,f241,f234,f274,f248,f6003,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f6003,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl10_632 ),
    inference(avatar_component_clause,[],[f6002])).

fof(f6002,plain,
    ( spl10_632
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_632])])).

fof(f274,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl10_32
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f6071,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_7
    | spl10_9
    | spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | spl10_25
    | ~ spl10_32
    | ~ spl10_642 ),
    inference(avatar_contradiction_clause,[],[f6065])).

fof(f6065,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_25
    | ~ spl10_32
    | ~ spl10_642 ),
    inference(unit_resulting_resolution,[],[f164,f171,f178,f185,f192,f199,f227,f241,f234,f274,f248,f6057,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f6057,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_642 ),
    inference(avatar_component_clause,[],[f6056])).

fof(f6056,plain,
    ( spl10_642
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_642])])).

fof(f6064,plain,
    ( spl10_642
    | spl10_644
    | spl10_9
    | ~ spl10_20
    | ~ spl10_336
    | ~ spl10_346
    | ~ spl10_630 ),
    inference(avatar_split_clause,[],[f6037,f5996,f2875,f2842,f233,f191,f6062,f6056])).

fof(f6062,plain,
    ( spl10_644
  <=> u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_644])])).

fof(f6037,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | r1_tsep_1(sK2,sK3)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_336
    | ~ spl10_346
    | ~ spl10_630 ),
    inference(forward_demodulation,[],[f2894,f5997])).

fof(f2894,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_tsep_1(sK2,sK3)
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_336
    | ~ spl10_346 ),
    inference(forward_demodulation,[],[f2893,f129])).

fof(f2893,plain,
    ( r1_tsep_1(sK2,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_336
    | ~ spl10_346 ),
    inference(subsumption_resolution,[],[f2892,f192])).

fof(f2892,plain,
    ( r1_tsep_1(sK2,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl10_20
    | ~ spl10_336
    | ~ spl10_346 ),
    inference(subsumption_resolution,[],[f2888,f234])).

fof(f2888,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK2,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK3,sK2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl10_336
    | ~ spl10_346 ),
    inference(resolution,[],[f2876,f2843])).

fof(f2876,plain,
    ( ! [X12] :
        ( ~ l1_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | r1_tsep_1(X12,sK3)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X12)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X12))
        | v2_struct_0(X12) )
    | ~ spl10_346 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f6004,plain,
    ( spl10_630
    | spl10_632
    | spl10_11
    | ~ spl10_22
    | ~ spl10_338
    | ~ spl10_344 ),
    inference(avatar_split_clause,[],[f2885,f2869,f2848,f240,f198,f6002,f5996])).

fof(f2885,plain,
    ( r1_tsep_1(sK3,sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_11
    | ~ spl10_22
    | ~ spl10_338
    | ~ spl10_344 ),
    inference(subsumption_resolution,[],[f2884,f199])).

fof(f2884,plain,
    ( r1_tsep_1(sK3,sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ spl10_22
    | ~ spl10_338
    | ~ spl10_344 ),
    inference(subsumption_resolution,[],[f2883,f241])).

fof(f2883,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | r1_tsep_1(sK3,sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ spl10_338
    | ~ spl10_344 ),
    inference(resolution,[],[f2870,f2849])).

fof(f2849,plain,
    ( ! [X12] :
        ( ~ l1_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | r1_tsep_1(X12,sK2)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X12)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X12))
        | v2_struct_0(X12) )
    | ~ spl10_338 ),
    inference(avatar_component_clause,[],[f2848])).

fof(f3743,plain,
    ( spl10_434
    | ~ spl10_32
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f2302,f322,f273,f3741])).

fof(f2302,plain,
    ( ! [X9] : r1_tarski(k3_xboole_0(u1_struct_0(sK1),X9),k3_xboole_0(u1_struct_0(sK3),X9))
    | ~ spl10_32
    | ~ spl10_42 ),
    inference(subsumption_resolution,[],[f2296,f323])).

fof(f2296,plain,
    ( ! [X9] :
        ( ~ l1_pre_topc(sK3)
        | r1_tarski(k3_xboole_0(u1_struct_0(sK1),X9),k3_xboole_0(u1_struct_0(sK3),X9)) )
    | ~ spl10_32 ),
    inference(resolution,[],[f557,f274])).

fof(f2882,plain,
    ( ~ spl10_42
    | spl10_345 ),
    inference(avatar_contradiction_clause,[],[f2881])).

fof(f2881,plain,
    ( $false
    | ~ spl10_42
    | ~ spl10_345 ),
    inference(subsumption_resolution,[],[f2879,f323])).

fof(f2879,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl10_345 ),
    inference(resolution,[],[f2873,f113])).

fof(f113,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',dt_l1_pre_topc)).

fof(f2873,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl10_345 ),
    inference(avatar_component_clause,[],[f2872])).

fof(f2872,plain,
    ( spl10_345
  <=> ~ l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_345])])).

fof(f2855,plain,
    ( ~ spl10_40
    | spl10_337 ),
    inference(avatar_contradiction_clause,[],[f2854])).

fof(f2854,plain,
    ( $false
    | ~ spl10_40
    | ~ spl10_337 ),
    inference(subsumption_resolution,[],[f2852,f314])).

fof(f314,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl10_40
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f2852,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl10_337 ),
    inference(resolution,[],[f2846,f113])).

fof(f2846,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl10_337 ),
    inference(avatar_component_clause,[],[f2845])).

fof(f2845,plain,
    ( spl10_337
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_337])])).

fof(f2236,plain,
    ( spl10_264
    | spl10_266
    | spl10_11
    | ~ spl10_22
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f815,f742,f240,f198,f2234,f2228])).

fof(f742,plain,
    ( spl10_94
  <=> ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f815,plain,
    ( r1_tsep_1(sK1,sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_11
    | ~ spl10_22
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f808,f199])).

fof(f808,plain,
    ( r1_tsep_1(sK1,sK3)
    | v2_struct_0(sK3)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK3)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl10_22
    | ~ spl10_94 ),
    inference(resolution,[],[f743,f241])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(sK1,X0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f742])).

fof(f1772,plain,
    ( spl10_210
    | spl10_9
    | ~ spl10_20
    | spl10_25
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f814,f742,f247,f233,f191,f1770])).

fof(f814,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_9
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f813,f192])).

fof(f813,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_20
    | ~ spl10_25
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f807,f248])).

fof(f807,plain,
    ( r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK2)
    | u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl10_20
    | ~ spl10_94 ),
    inference(resolution,[],[f743,f234])).

fof(f797,plain,
    ( ~ spl10_107
    | spl10_35 ),
    inference(avatar_split_clause,[],[f787,f276,f795])).

fof(f276,plain,
    ( spl10_35
  <=> ~ m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f787,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ spl10_35 ),
    inference(subsumption_resolution,[],[f107,f277])).

fof(f277,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f276])).

fof(f107,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f84])).

fof(f758,plain,
    ( spl10_100
    | spl10_1
    | ~ spl10_4
    | spl10_11
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f486,f240,f198,f177,f163,f756])).

fof(f486,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f485,f164])).

fof(f485,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f484,f178])).

fof(f484,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_11
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f472,f199])).

fof(f472,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | u1_struct_0(k2_tsep_1(sK0,sK3,X2)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(X2))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_22 ),
    inference(resolution,[],[f467,f241])).

fof(f467,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f466,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f466,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f465,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f465,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f154,f149])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',d5_tsep_1)).

fof(f750,plain,
    ( spl10_96
    | spl10_1
    | ~ spl10_4
    | spl10_9
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f483,f233,f191,f177,f163,f748])).

fof(f483,plain,
    ( ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f482,f164])).

fof(f482,plain,
    ( ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f481,f178])).

fof(f481,plain,
    ( ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_9
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f471,f192])).

fof(f471,plain,
    ( ! [X1] :
        ( r1_tsep_1(sK2,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | u1_struct_0(k2_tsep_1(sK0,sK2,X1)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(X1))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_20 ),
    inference(resolution,[],[f467,f234])).

fof(f744,plain,
    ( spl10_94
    | spl10_1
    | ~ spl10_4
    | spl10_7
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f480,f226,f184,f177,f163,f742])).

fof(f480,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0)) )
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f479,f164])).

fof(f479,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f478,f178])).

fof(f478,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_7
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f470,f185])).

fof(f470,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | u1_struct_0(k2_tsep_1(sK0,sK1,X0)) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_18 ),
    inference(resolution,[],[f467,f227])).

fof(f380,plain,
    ( spl10_32
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f108,f378,f273])).

fof(f108,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f324,plain,
    ( spl10_42
    | ~ spl10_22
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f298,f291,f240,f322])).

fof(f291,plain,
    ( spl10_36
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f298,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_22
    | ~ spl10_36 ),
    inference(resolution,[],[f292,f241])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f291])).

fof(f315,plain,
    ( spl10_40
    | ~ spl10_20
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f297,f291,f233,f313])).

fof(f297,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_20
    | ~ spl10_36 ),
    inference(resolution,[],[f292,f234])).

fof(f293,plain,
    ( spl10_36
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f284,f177,f291])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f116,f178])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t32_tmap_1.p',dt_m1_pre_topc)).

fof(f281,plain,
    ( spl10_32
    | spl10_34 ),
    inference(avatar_split_clause,[],[f106,f279,f273])).

fof(f106,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f249,plain,(
    ~ spl10_25 ),
    inference(avatar_split_clause,[],[f105,f247])).

fof(f105,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f84])).

fof(f242,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f104,f240])).

fof(f104,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f235,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f102,f233])).

fof(f102,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f228,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f100,f226])).

fof(f100,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f200,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f103,f198])).

fof(f103,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f193,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f101,f191])).

fof(f101,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

fof(f186,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f99,f184])).

fof(f99,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

fof(f179,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f98,f177])).

fof(f98,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f172,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f97,f170])).

fof(f97,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f84])).

fof(f165,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f96,f163])).

fof(f96,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).
%------------------------------------------------------------------------------

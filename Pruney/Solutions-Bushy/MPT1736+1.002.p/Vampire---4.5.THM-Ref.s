%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1736+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:27 EST 2020

% Result     : Theorem 5.67s
% Output     : Refutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 596 expanded)
%              Number of leaves         :   46 ( 253 expanded)
%              Depth                    :   19
%              Number of atoms          : 1376 (4575 expanded)
%              Number of equality atoms :   22 (  59 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f181,f186,f198,f230,f378,f520,f575,f585,f836,f866,f972,f994,f1878,f9580,f9588])).

fof(f9588,plain,
    ( k1_tsep_1(sK5,sK7,sK6) != k1_tsep_1(sK5,sK6,sK7)
    | v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
    | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9580,plain,
    ( ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | spl9_18
    | spl9_23
    | spl9_222 ),
    inference(avatar_contradiction_clause,[],[f9579])).

fof(f9579,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | spl9_18
    | spl9_23
    | spl9_222 ),
    inference(subsumption_resolution,[],[f9527,f229])).

fof(f229,plain,
    ( ~ sP2(k1_tsep_1(sK5,sK6,sK7),sK6)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl9_23
  <=> sP2(k1_tsep_1(sK5,sK6,sK7),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f9527,plain,
    ( sP2(k1_tsep_1(sK5,sK6,sK7),sK6)
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | spl9_18
    | spl9_222 ),
    inference(unit_resulting_resolution,[],[f150,f170,f185,f160,f180,f175,f140,f165,f155,f135,f197,f145,f1877,f6906])).

fof(f6906,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(k1_tsep_1(X1,X2,X3),X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | r1_tsep_1(X0,k1_tsep_1(X1,X2,X3)) ) ),
    inference(subsumption_resolution,[],[f6905,f1523])).

fof(f1523,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X0,X2,X3))
      | r1_tsep_1(X1,k1_tsep_1(X0,X2,X3))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(X1,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1522,f995])).

fof(f995,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_struct_0(k1_tsep_1(X3,X5,X4))
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f945,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f945,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_struct_0(k1_tsep_1(X3,X5,X4))
      | ~ sP4(X3,X5,X4)
      | ~ m1_pre_topc(X4,X3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f104,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f1522,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X0,X2,X3))
      | r1_tsep_1(X1,k1_tsep_1(X0,X2,X3))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(k1_tsep_1(X0,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(X1,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1509,f997])).

fof(f997,plain,(
    ! [X10,X11,X9] :
      ( m1_pre_topc(k1_tsep_1(X9,X11,X10),X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f947,f107])).

fof(f947,plain,(
    ! [X10,X11,X9] :
      ( m1_pre_topc(k1_tsep_1(X9,X11,X10),X9)
      | ~ sP4(X9,X11,X10)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(superposition,[],[f106,f103])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1509,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X0,X2,X3))
      | r1_tsep_1(X1,k1_tsep_1(X0,X2,X3))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(k1_tsep_1(X0,X2,X3),X0)
      | v2_struct_0(k1_tsep_1(X0,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(X1,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f1506])).

fof(f1506,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X0,X2,X3))
      | r1_tsep_1(X1,k1_tsep_1(X0,X2,X3))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(k1_tsep_1(X0,X2,X3),X0)
      | v2_struct_0(k1_tsep_1(X0,X2,X3))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(X1,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f81,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
      | sP0(X2,X3)
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | sP0(X2,X3)
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
    inference(definition_folding,[],[f26,f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( ( ~ r1_tsep_1(X3,X2)
        & ~ r1_tsep_1(X2,X3) )
      | ~ sP0(X2,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tmap_1)).

fof(f6905,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X1,X2,X3))
      | sP2(k1_tsep_1(X1,X2,X3),X2) ) ),
    inference(subsumption_resolution,[],[f6904,f998])).

fof(f998,plain,(
    ! [X14,X12,X13] :
      ( v2_pre_topc(k1_tsep_1(X12,X14,X13))
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X14,X12)
      | v2_struct_0(X14)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f951,f107])).

fof(f951,plain,(
    ! [X14,X12,X13] :
      ( v2_pre_topc(k1_tsep_1(X12,X14,X13))
      | ~ sP4(X12,X14,X13)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X14,X12)
      | v2_struct_0(X14)
      | v2_struct_0(X12) ) ),
    inference(duplicate_literal_removal,[],[f948])).

fof(f948,plain,(
    ! [X14,X12,X13] :
      ( v2_pre_topc(k1_tsep_1(X12,X14,X13))
      | ~ sP4(X12,X14,X13)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X14,X12)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X12) ) ),
    inference(superposition,[],[f352,f103])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f106,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f6904,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X1,X2,X3))
      | sP2(k1_tsep_1(X1,X2,X3),X2) ) ),
    inference(subsumption_resolution,[],[f6903,f999])).

fof(f999,plain,(
    ! [X17,X15,X16] :
      ( l1_pre_topc(k1_tsep_1(X15,X17,X16))
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X17,X15)
      | v2_struct_0(X17)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f950,f107])).

fof(f950,plain,(
    ! [X17,X15,X16] :
      ( l1_pre_topc(k1_tsep_1(X15,X17,X16))
      | ~ sP4(X15,X17,X16)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X17,X15)
      | v2_struct_0(X17)
      | v2_struct_0(X15) ) ),
    inference(duplicate_literal_removal,[],[f949])).

fof(f949,plain,(
    ! [X17,X15,X16] :
      ( l1_pre_topc(k1_tsep_1(X15,X17,X16))
      | ~ sP4(X15,X17,X16)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X17,X15)
      | v2_struct_0(X17)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(superposition,[],[f353,f103])).

fof(f353,plain,(
    ! [X4,X5,X3] :
      ( l1_pre_topc(k1_tsep_1(X3,X5,X4))
      | ~ sP4(X3,X4,X5)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f6903,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ v2_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X1,X2,X3))
      | sP2(k1_tsep_1(X1,X2,X3),X2) ) ),
    inference(subsumption_resolution,[],[f6902,f79])).

fof(f6902,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ v2_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X1,X2,X3))
      | sP2(k1_tsep_1(X1,X2,X3),X2) ) ),
    inference(subsumption_resolution,[],[f6886,f93])).

fof(f6886,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_borsuk_1(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X3)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ v2_pre_topc(k1_tsep_1(X1,X2,X3))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X1,X2,X3))
      | sP2(k1_tsep_1(X1,X2,X3),X2) ) ),
    inference(resolution,[],[f1525,f1255])).

fof(f1255,plain,(
    ! [X0,X1] :
      ( ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | sP2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1254,f93])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(subsumption_resolution,[],[f1253,f79])).

fof(f1253,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(resolution,[],[f108,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_borsuk_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_borsuk_1(X1,X0) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X2] :
      ( ( sP3(X0,X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_borsuk_1(X2,X0) )
      & ( ( m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0) )
        | ~ sP3(X0,X2) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X2] :
      ( ( sP3(X0,X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_borsuk_1(X2,X0) )
      & ( ( m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0) )
        | ~ sP3(X0,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X2] :
      ( sP3(X0,X2)
    <=> ( m1_pre_topc(X2,X0)
        & v1_borsuk_1(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | sP2(X0,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1)
      | ~ sP3(X0,X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP2(X0,X1)
                  | ~ sP3(X0,X2) )
                & ( sP3(X0,X2)
                  | ~ sP2(X0,X1) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP2(X0,X1)
              <=> sP3(X0,X2) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f32,f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_borsuk_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f1525,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),k1_tsep_1(X4,X6,X7))
      | r1_tsep_1(X5,k1_tsep_1(X4,X6,X7))
      | ~ m1_pre_topc(X5,X4)
      | ~ v1_borsuk_1(X5,X4)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | sP0(X5,X7)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X7,X4)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X6,X4)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f1524,f995])).

fof(f1524,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),k1_tsep_1(X4,X6,X7))
      | r1_tsep_1(X5,k1_tsep_1(X4,X6,X7))
      | ~ m1_pre_topc(X5,X4)
      | ~ v1_borsuk_1(X5,X4)
      | v2_struct_0(X5)
      | v2_struct_0(k1_tsep_1(X4,X6,X7))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | sP0(X5,X7)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X7,X4)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X6,X4)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f1508,f997])).

fof(f1508,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),k1_tsep_1(X4,X6,X7))
      | r1_tsep_1(X5,k1_tsep_1(X4,X6,X7))
      | ~ m1_pre_topc(X5,X4)
      | ~ v1_borsuk_1(X5,X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(k1_tsep_1(X4,X6,X7),X4)
      | v2_struct_0(k1_tsep_1(X4,X6,X7))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | sP0(X5,X7)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X7,X4)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X6,X4)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f1507])).

fof(f1507,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_borsuk_1(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),k1_tsep_1(X4,X6,X7))
      | r1_tsep_1(X5,k1_tsep_1(X4,X6,X7))
      | ~ m1_pre_topc(X5,X4)
      | ~ v1_borsuk_1(X5,X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(k1_tsep_1(X4,X6,X7),X4)
      | v2_struct_0(k1_tsep_1(X4,X6,X7))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | sP0(X5,X7)
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(X7,X4)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,X4)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f80,f87])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1877,plain,
    ( ~ r1_tsep_1(sK8,k1_tsep_1(sK5,sK6,sK7))
    | spl9_222 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f1875,plain,
    ( spl9_222
  <=> r1_tsep_1(sK8,k1_tsep_1(sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f145,plain,
    ( v1_borsuk_1(sK8,sK5)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_8
  <=> v1_borsuk_1(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f197,plain,
    ( ~ sP0(sK8,sK7)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl9_18
  <=> sP0(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f135,plain,
    ( m1_pre_topc(sK6,sK8)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl9_6
  <=> m1_pre_topc(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f155,plain,
    ( m1_pre_topc(sK7,sK5)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_10
  <=> m1_pre_topc(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f165,plain,
    ( m1_pre_topc(sK6,sK5)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl9_12
  <=> m1_pre_topc(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f140,plain,
    ( m1_pre_topc(sK8,sK5)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_7
  <=> m1_pre_topc(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f175,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl9_14
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f180,plain,
    ( v2_pre_topc(sK5)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl9_15
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f160,plain,
    ( ~ v2_struct_0(sK7)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl9_11
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f185,plain,
    ( ~ v2_struct_0(sK5)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl9_16
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f170,plain,
    ( ~ v2_struct_0(sK6)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl9_13
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f150,plain,
    ( ~ v2_struct_0(sK8)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_9
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1878,plain,
    ( ~ spl9_222
    | ~ spl9_2
    | ~ spl9_7
    | spl9_9
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | spl9_65
    | ~ spl9_67
    | spl9_112 ),
    inference(avatar_split_clause,[],[f1780,f863,f582,f572,f183,f178,f173,f168,f163,f148,f138,f115,f1875])).

fof(f115,plain,
    ( spl9_2
  <=> m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f572,plain,
    ( spl9_65
  <=> v2_struct_0(k1_tsep_1(sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f582,plain,
    ( spl9_67
  <=> m1_pre_topc(k1_tsep_1(sK5,sK6,sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f863,plain,
    ( spl9_112
  <=> sP1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f1780,plain,
    ( ~ r1_tsep_1(sK8,k1_tsep_1(sK5,sK6,sK7))
    | ~ spl9_2
    | ~ spl9_7
    | spl9_9
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | spl9_65
    | ~ spl9_67
    | spl9_112 ),
    inference(unit_resulting_resolution,[],[f185,f180,f175,f170,f150,f140,f865,f165,f574,f116,f584,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X3)
      | ~ r1_tsep_1(X3,X2)
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | sP1(X1,X3)
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
    inference(definition_folding,[],[f28,f41])).

fof(f41,plain,(
    ! [X1,X3] :
      ( ( r1_tsep_1(X3,X1)
        & r1_tsep_1(X1,X3) )
      | ~ sP1(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f584,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK7),sK5)
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f582])).

fof(f116,plain,
    ( m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f574,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | spl9_65 ),
    inference(avatar_component_clause,[],[f572])).

fof(f865,plain,
    ( ~ sP1(sK6,sK8)
    | spl9_112 ),
    inference(avatar_component_clause,[],[f863])).

fof(f994,plain,
    ( ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(subsumption_resolution,[],[f992,f185])).

fof(f992,plain,
    ( v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f991,f175])).

fof(f991,plain,
    ( ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13 ),
    inference(subsumption_resolution,[],[f990,f170])).

fof(f990,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f989,f165])).

fof(f989,plain,
    ( ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10
    | spl9_11 ),
    inference(subsumption_resolution,[],[f988,f160])).

fof(f988,plain,
    ( v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f987,f155])).

fof(f987,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl9_2
    | spl9_4 ),
    inference(subsumption_resolution,[],[f938,f116])).

fof(f938,plain,
    ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_pre_topc(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK5)
    | v2_struct_0(sK5)
    | spl9_4 ),
    inference(superposition,[],[f125,f103])).

fof(f125,plain,
    ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_4
  <=> m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f972,plain,
    ( spl9_119
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(avatar_split_clause,[],[f915,f183,f173,f168,f163,f158,f153,f962])).

fof(f962,plain,
    ( spl9_119
  <=> k1_tsep_1(sK5,sK7,sK6) = k1_tsep_1(sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f915,plain,
    ( k1_tsep_1(sK5,sK7,sK6) = k1_tsep_1(sK5,sK6,sK7)
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f185,f175,f160,f155,f170,f165,f103])).

fof(f866,plain,
    ( ~ spl9_112
    | spl9_108 ),
    inference(avatar_split_clause,[],[f860,f833,f863])).

fof(f833,plain,
    ( spl9_108
  <=> r1_tsep_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f860,plain,
    ( ~ sP1(sK6,sK8)
    | spl9_108 ),
    inference(unit_resulting_resolution,[],[f835,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X0,X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X3] :
      ( ( r1_tsep_1(X3,X1)
        & r1_tsep_1(X1,X3) )
      | ~ sP1(X1,X3) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f835,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | spl9_108 ),
    inference(avatar_component_clause,[],[f833])).

fof(f836,plain,
    ( ~ spl9_108
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f816,f183,f178,f173,f168,f163,f148,f138,f133,f833])).

fof(f816,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | ~ spl9_6
    | ~ spl9_7
    | spl9_9
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f185,f180,f175,f170,f150,f165,f140,f135,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f585,plain,
    ( spl9_67
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f568,f375,f582])).

fof(f375,plain,
    ( spl9_38
  <=> sP4(sK5,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f568,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK6,sK7),sK5)
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f377,f106])).

fof(f377,plain,
    ( sP4(sK5,sK7,sK6)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f375])).

fof(f575,plain,
    ( ~ spl9_65
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f570,f375,f572])).

fof(f570,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK5,sK6,sK7))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f377,f104])).

fof(f520,plain,
    ( spl9_2
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f481,f183,f178,f173,f168,f163,f158,f153,f115])).

fof(f481,plain,
    ( m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f185,f180,f175,f170,f165,f160,f155,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f378,plain,
    ( spl9_38
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(avatar_split_clause,[],[f361,f183,f173,f168,f163,f158,f153,f375])).

fof(f361,plain,
    ( sP4(sK5,sK7,sK6)
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f185,f175,f170,f165,f160,f155,f107])).

fof(f230,plain,
    ( ~ spl9_23
    | spl9_1 ),
    inference(avatar_split_clause,[],[f219,f111,f227])).

fof(f111,plain,
    ( spl9_1
  <=> v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f219,plain,
    ( ~ sP2(k1_tsep_1(sK5,sK6,sK7),sK6)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f113,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_borsuk_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_borsuk_1(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_borsuk_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_borsuk_1(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f113,plain,
    ( ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f198,plain,
    ( ~ spl9_18
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f193,f128,f195])).

fof(f128,plain,
    ( spl9_5
  <=> r1_tsep_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f193,plain,
    ( ~ sP0(sK8,sK7)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f130,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_tsep_1(X1,X0)
        & ~ r1_tsep_1(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ( ~ r1_tsep_1(X3,X2)
        & ~ r1_tsep_1(X2,X3) )
      | ~ sP0(X2,X3) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f130,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f186,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f65,f183])).

fof(f65,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
      | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
      | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
      | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) )
    & r1_tsep_1(sK8,sK7)
    & m1_pre_topc(sK6,sK8)
    & m1_pre_topc(sK8,sK5)
    & v1_borsuk_1(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f51,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                      | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                    & r1_tsep_1(X3,X2)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK5,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(sK5,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(sK5,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(sK5,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK5)
                  & v1_borsuk_1(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK5,X2,X1))
                  | ~ v1_borsuk_1(X1,k1_tsep_1(sK5,X2,X1))
                  | ~ m1_pre_topc(X1,k1_tsep_1(sK5,X1,X2))
                  | ~ v1_borsuk_1(X1,k1_tsep_1(sK5,X1,X2)) )
                & r1_tsep_1(X3,X2)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK5)
                & v1_borsuk_1(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,X2,sK6))
                | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,X2,sK6))
                | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,X2))
                | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,X2)) )
              & r1_tsep_1(X3,X2)
              & m1_pre_topc(sK6,X3)
              & m1_pre_topc(X3,sK5)
              & v1_borsuk_1(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,X2,sK6))
              | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,X2,sK6))
              | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,X2))
              | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,X2)) )
            & r1_tsep_1(X3,X2)
            & m1_pre_topc(sK6,X3)
            & m1_pre_topc(X3,sK5)
            & v1_borsuk_1(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
            | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
            | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
            | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) )
          & r1_tsep_1(X3,sK7)
          & m1_pre_topc(sK6,X3)
          & m1_pre_topc(X3,sK5)
          & v1_borsuk_1(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
          | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
          | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
          | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) )
        & r1_tsep_1(X3,sK7)
        & m1_pre_topc(sK6,X3)
        & m1_pre_topc(X3,sK5)
        & v1_borsuk_1(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
        | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
        | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
        | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) )
      & r1_tsep_1(sK8,sK7)
      & m1_pre_topc(sK6,sK8)
      & m1_pre_topc(sK8,sK5)
      & v1_borsuk_1(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tmap_1)).

fof(f181,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f66,f178])).

fof(f66,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f176,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f67,f173])).

fof(f67,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f171,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f68,f168])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f166,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f69,f163])).

fof(f69,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f161,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f70,f158])).

fof(f70,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f156,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f71,f153])).

fof(f71,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f151,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f72,f148])).

fof(f72,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f146,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f73,f143])).

fof(f73,plain,(
    v1_borsuk_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f141,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f74,f138])).

fof(f74,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f75,f133])).

fof(f75,plain,(
    m1_pre_topc(sK6,sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f76,f128])).

fof(f76,plain,(
    r1_tsep_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f77,f123,f119,f115,f111])).

fof(f119,plain,
    ( spl9_3
  <=> v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f77,plain,
    ( ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK7,sK6))
    | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK7,sK6))
    | ~ m1_pre_topc(sK6,k1_tsep_1(sK5,sK6,sK7))
    | ~ v1_borsuk_1(sK6,k1_tsep_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------

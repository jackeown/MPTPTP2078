%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  298 ( 769 expanded)
%              Number of leaves         :   41 ( 267 expanded)
%              Depth                    :   37
%              Number of atoms          : 1479 (11289 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1782,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1463,f1467,f1471,f1480,f1484,f1488,f1491,f1495,f1564,f1713,f1716,f1781])).

fof(f1781,plain,(
    spl15_33 ),
    inference(avatar_contradiction_clause,[],[f1780])).

fof(f1780,plain,
    ( $false
    | spl15_33 ),
    inference(subsumption_resolution,[],[f1779,f247])).

fof(f247,plain,(
    sP3(sK11,sK12) ),
    inference(subsumption_resolution,[],[f245,f105])).

fof(f105,plain,(
    l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ! [X3] :
        ( ~ r1_subset_1(sK12,X3)
        | ~ r1_tarski(sK13,X3)
        | ~ v2_waybel_7(X3,sK11)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
        | ~ v13_waybel_0(X3,sK11)
        | ~ v2_waybel_0(X3,sK11)
        | v1_xboole_0(X3) )
    & r1_subset_1(sK12,sK13)
    & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK11)))
    & v13_waybel_0(sK13,sK11)
    & v2_waybel_0(sK13,sK11)
    & ~ v1_xboole_0(sK13)
    & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK11)))
    & v12_waybel_0(sK12,sK11)
    & v1_waybel_0(sK12,sK11)
    & ~ v1_xboole_0(sK12)
    & l1_orders_2(sK11)
    & v2_lattice3(sK11)
    & v1_lattice3(sK11)
    & v2_waybel_1(sK11)
    & v5_orders_2(sK11)
    & v4_orders_2(sK11)
    & v3_orders_2(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f25,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_subset_1(X1,X3)
                    | ~ r1_tarski(X2,X3)
                    | ~ v2_waybel_7(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v13_waybel_0(X3,X0)
                    | ~ v2_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                & r1_subset_1(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,sK11)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
                  | ~ v13_waybel_0(X3,sK11)
                  | ~ v2_waybel_0(X3,sK11)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK11)))
              & v13_waybel_0(X2,sK11)
              & v2_waybel_0(X2,sK11)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK11)))
          & v12_waybel_0(X1,sK11)
          & v1_waybel_0(X1,sK11)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK11)
      & v2_lattice3(sK11)
      & v1_lattice3(sK11)
      & v2_waybel_1(sK11)
      & v5_orders_2(sK11)
      & v4_orders_2(sK11)
      & v3_orders_2(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_subset_1(X1,X3)
                | ~ r1_tarski(X2,X3)
                | ~ v2_waybel_7(X3,sK11)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
                | ~ v13_waybel_0(X3,sK11)
                | ~ v2_waybel_0(X3,sK11)
                | v1_xboole_0(X3) )
            & r1_subset_1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK11)))
            & v13_waybel_0(X2,sK11)
            & v2_waybel_0(X2,sK11)
            & ~ v1_xboole_0(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK11)))
        & v12_waybel_0(X1,sK11)
        & v1_waybel_0(X1,sK11)
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_subset_1(sK12,X3)
              | ~ r1_tarski(X2,X3)
              | ~ v2_waybel_7(X3,sK11)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
              | ~ v13_waybel_0(X3,sK11)
              | ~ v2_waybel_0(X3,sK11)
              | v1_xboole_0(X3) )
          & r1_subset_1(sK12,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK11)))
          & v13_waybel_0(X2,sK11)
          & v2_waybel_0(X2,sK11)
          & ~ v1_xboole_0(X2) )
      & m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK11)))
      & v12_waybel_0(sK12,sK11)
      & v1_waybel_0(sK12,sK11)
      & ~ v1_xboole_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_subset_1(sK12,X3)
            | ~ r1_tarski(X2,X3)
            | ~ v2_waybel_7(X3,sK11)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
            | ~ v13_waybel_0(X3,sK11)
            | ~ v2_waybel_0(X3,sK11)
            | v1_xboole_0(X3) )
        & r1_subset_1(sK12,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK11)))
        & v13_waybel_0(X2,sK11)
        & v2_waybel_0(X2,sK11)
        & ~ v1_xboole_0(X2) )
   => ( ! [X3] :
          ( ~ r1_subset_1(sK12,X3)
          | ~ r1_tarski(sK13,X3)
          | ~ v2_waybel_7(X3,sK11)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
          | ~ v13_waybel_0(X3,sK11)
          | ~ v2_waybel_0(X3,sK11)
          | v1_xboole_0(X3) )
      & r1_subset_1(sK12,sK13)
      & m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK11)))
      & v13_waybel_0(sK13,sK11)
      & v2_waybel_0(sK13,sK11)
      & ~ v1_xboole_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_subset_1(X1,X3)
                  | ~ r1_tarski(X2,X3)
                  | ~ v2_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v13_waybel_0(X3,X0)
                  | ~ v2_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & r1_subset_1(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v13_waybel_0(X3,X0)
                          & v2_waybel_0(X3,X0)
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_subset_1(X1,X3)
                            & r1_tarski(X2,X3)
                            & v2_waybel_7(X3,X0) ) )
                    & r1_subset_1(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_7)).

fof(f245,plain,
    ( sP3(sK11,sK12)
    | ~ l1_orders_2(sK11) ),
    inference(resolution,[],[f232,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | sP3(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP2(X0,X1)
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | ~ sP2(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
        <=> sP3(X0,X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f28,f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_7)).

fof(f232,plain,(
    sP2(sK11,sK12) ),
    inference(subsumption_resolution,[],[f220,f108])).

fof(f108,plain,(
    v12_waybel_0(sK12,sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f220,plain,
    ( sP2(sK11,sK12)
    | ~ v12_waybel_0(sK12,sK11) ),
    inference(resolution,[],[f130,f109])).

fof(f109,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(u1_struct_0(sK11))) ),
    inference(cnf_transformation,[],[f69])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X0,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v12_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f1779,plain,
    ( ~ sP3(sK11,sK12)
    | spl15_33 ),
    inference(resolution,[],[f1712,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v13_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v13_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f1712,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | spl15_33 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1710,plain,
    ( spl15_33
  <=> v13_waybel_0(sK12,k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_33])])).

fof(f1716,plain,(
    spl15_32 ),
    inference(avatar_contradiction_clause,[],[f1715])).

fof(f1715,plain,
    ( $false
    | spl15_32 ),
    inference(subsumption_resolution,[],[f1714,f210])).

fof(f210,plain,(
    sP1(sK11,sK12) ),
    inference(subsumption_resolution,[],[f208,f105])).

fof(f208,plain,
    ( sP1(sK11,sK12)
    | ~ l1_orders_2(sK11) ),
    inference(resolution,[],[f196,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | sP1(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | ~ sP0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> sP1(X0,X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f27,f50,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_0(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_7)).

fof(f196,plain,(
    sP0(sK11,sK12) ),
    inference(subsumption_resolution,[],[f184,f107])).

fof(f107,plain,(
    v1_waybel_0(sK12,sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f184,plain,
    ( sP0(sK11,sK12)
    | ~ v1_waybel_0(sK12,sK11) ),
    inference(resolution,[],[f122,f109])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1)
      | ~ v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_0(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f1714,plain,
    ( ~ sP1(sK11,sK12)
    | spl15_32 ),
    inference(resolution,[],[f1708,f327])).

fof(f327,plain,(
    ! [X19,X18] :
      ( sP7(k7_lattice3(X18),X19)
      | ~ sP1(X18,X19) ) ),
    inference(subsumption_resolution,[],[f315,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v2_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v2_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f315,plain,(
    ! [X19,X18] :
      ( sP7(k7_lattice3(X18),X19)
      | ~ v2_waybel_0(X19,k7_lattice3(X18))
      | ~ sP1(X18,X19) ) ),
    inference(resolution,[],[f143,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP7(X0,X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( sP7(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_0(X1,X0) )
        | ~ sP7(X0,X1) ) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( sP7(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_0(X1,X0) )
        | ~ sP7(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP7(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f1708,plain,
    ( ~ sP7(k7_lattice3(sK11),sK12)
    | spl15_32 ),
    inference(avatar_component_clause,[],[f1706])).

fof(f1706,plain,
    ( spl15_32
  <=> sP7(k7_lattice3(sK11),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f1713,plain,
    ( ~ spl15_32
    | ~ spl15_33
    | ~ spl15_11
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(avatar_split_clause,[],[f1704,f1456,f1452,f1448,f1444,f1440,f1436,f1432,f1428,f1420,f1710,f1706])).

fof(f1420,plain,
    ( spl15_11
  <=> sP2(k7_lattice3(sK11),sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_11])])).

fof(f1428,plain,
    ( spl15_13
  <=> v3_orders_2(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_13])])).

fof(f1432,plain,
    ( spl15_14
  <=> v4_orders_2(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f1436,plain,
    ( spl15_15
  <=> v5_orders_2(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1440,plain,
    ( spl15_16
  <=> v2_waybel_1(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f1444,plain,
    ( spl15_17
  <=> v1_lattice3(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f1448,plain,
    ( spl15_18
  <=> v2_lattice3(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f1452,plain,
    ( spl15_19
  <=> l1_orders_2(k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f1456,plain,
    ( spl15_20
  <=> v1_waybel_0(sK13,k7_lattice3(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f1704,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ spl15_11
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1703,f1421])).

fof(f1421,plain,
    ( sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_11 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1703,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_13
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1702,f1429])).

fof(f1429,plain,
    ( v3_orders_2(k7_lattice3(sK11))
    | ~ spl15_13 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1702,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_14
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1701,f1433])).

fof(f1433,plain,
    ( v4_orders_2(k7_lattice3(sK11))
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1701,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_15
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1700,f1437])).

fof(f1437,plain,
    ( v5_orders_2(k7_lattice3(sK11))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1700,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_16
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1699,f1441])).

fof(f1441,plain,
    ( v2_waybel_1(k7_lattice3(sK11))
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f1699,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_17
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1698,f1445])).

fof(f1445,plain,
    ( v1_lattice3(k7_lattice3(sK11))
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1698,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_18
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1697,f1449])).

fof(f1449,plain,
    ( v2_lattice3(k7_lattice3(sK11))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f1448])).

fof(f1697,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_19
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1696,f1453])).

fof(f1453,plain,
    ( l1_orders_2(k7_lattice3(sK11))
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1696,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ l1_orders_2(k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1695,f110])).

fof(f110,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f69])).

fof(f1695,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | v1_xboole_0(sK13)
    | ~ l1_orders_2(k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13)
    | ~ spl15_20 ),
    inference(subsumption_resolution,[],[f1694,f1457])).

fof(f1457,plain,
    ( v1_waybel_0(sK13,k7_lattice3(sK11))
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1694,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ v1_waybel_0(sK13,k7_lattice3(sK11))
    | v1_xboole_0(sK13)
    | ~ l1_orders_2(k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13) ),
    inference(subsumption_resolution,[],[f1693,f181])).

fof(f181,plain,(
    r1_subset_1(sK13,sK12) ),
    inference(subsumption_resolution,[],[f180,f106])).

fof(f106,plain,(
    ~ v1_xboole_0(sK12) ),
    inference(cnf_transformation,[],[f69])).

fof(f180,plain,
    ( r1_subset_1(sK13,sK12)
    | v1_xboole_0(sK12) ),
    inference(subsumption_resolution,[],[f178,f110])).

fof(f178,plain,
    ( r1_subset_1(sK13,sK12)
    | v1_xboole_0(sK13)
    | v1_xboole_0(sK12) ),
    inference(resolution,[],[f177,f114])).

fof(f114,plain,(
    r1_subset_1(sK12,sK13) ),
    inference(cnf_transformation,[],[f69])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f1693,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | ~ r1_subset_1(sK13,sK12)
    | ~ v1_waybel_0(sK13,k7_lattice3(sK11))
    | v1_xboole_0(sK13)
    | ~ l1_orders_2(k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13) ),
    inference(subsumption_resolution,[],[f1692,f106])).

fof(f1692,plain,
    ( ~ v13_waybel_0(sK12,k7_lattice3(sK11))
    | v1_xboole_0(sK12)
    | ~ r1_subset_1(sK13,sK12)
    | ~ v1_waybel_0(sK13,k7_lattice3(sK11))
    | v1_xboole_0(sK13)
    | ~ l1_orders_2(k7_lattice3(sK11))
    | ~ v2_lattice3(k7_lattice3(sK11))
    | ~ v1_lattice3(k7_lattice3(sK11))
    | ~ v2_waybel_1(k7_lattice3(sK11))
    | ~ v5_orders_2(k7_lattice3(sK11))
    | ~ v4_orders_2(k7_lattice3(sK11))
    | ~ v3_orders_2(k7_lattice3(sK11))
    | ~ sP7(k7_lattice3(sK11),sK12)
    | ~ sP2(k7_lattice3(sK11),sK13) ),
    inference(resolution,[],[f1645,f946])).

fof(f946,plain,(
    ~ sP8(sK12,sK13,k7_lattice3(sK11)) ),
    inference(subsumption_resolution,[],[f945,f106])).

fof(f945,plain,
    ( ~ sP8(sK12,sK13,k7_lattice3(sK11))
    | v1_xboole_0(sK12) ),
    inference(duplicate_literal_removal,[],[f944])).

fof(f944,plain,
    ( ~ sP8(sK12,sK13,k7_lattice3(sK11))
    | v1_xboole_0(sK12)
    | ~ sP8(sK12,sK13,k7_lattice3(sK11)) ),
    inference(resolution,[],[f943,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(X0,sK14(X0,X1,X2))
      | v1_xboole_0(X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f179,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK14(X0,X1,X2))
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( r1_subset_1(sK14(X0,X1,X2),X0)
        & r1_tarski(X1,sK14(X0,X1,X2))
        & v1_waybel_7(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v12_waybel_0(sK14(X0,X1,X2),X2)
        & v1_waybel_0(sK14(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK14(X0,X1,X2)) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f91,f92])).

fof(f92,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X0)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v12_waybel_0(X3,X2)
          & v1_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(sK14(X0,X1,X2),X0)
        & r1_tarski(X1,sK14(X0,X1,X2))
        & v1_waybel_7(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v12_waybel_0(sK14(X0,X1,X2),X2)
        & v1_waybel_0(sK14(X0,X1,X2),X2)
        & ~ v1_xboole_0(sK14(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_subset_1(X3,X0)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v12_waybel_0(X3,X2)
          & v1_waybel_0(X3,X2)
          & ~ v1_xboole_0(X3) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X2)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP8(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X2)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
      | ~ sP8(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(X0,sK14(X0,X1,X2))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK14(X0,X1,X2))
      | ~ sP8(X0,X1,X2) ) ),
    inference(resolution,[],[f177,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(sK14(X0,X1,X2),X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f943,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK12,sK14(X0,sK13,k7_lattice3(sK11)))
      | ~ sP8(X0,sK13,k7_lattice3(sK11)) ) ),
    inference(duplicate_literal_removal,[],[f942])).

fof(f942,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK12,sK14(X0,sK13,k7_lattice3(sK11)))
      | ~ sP8(X0,sK13,k7_lattice3(sK11))
      | ~ sP8(X0,sK13,k7_lattice3(sK11)) ) ),
    inference(resolution,[],[f941,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK14(X0,X1,X2))
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f941,plain,(
    ! [X43,X42] :
      ( ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ sP8(X42,X43,k7_lattice3(sK11)) ) ),
    inference(subsumption_resolution,[],[f940,f99])).

fof(f99,plain,(
    v3_orders_2(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f940,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(subsumption_resolution,[],[f939,f100])).

fof(f100,plain,(
    v4_orders_2(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f939,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ v4_orders_2(sK11)
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(subsumption_resolution,[],[f938,f101])).

fof(f101,plain,(
    v5_orders_2(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f938,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ v5_orders_2(sK11)
      | ~ v4_orders_2(sK11)
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(subsumption_resolution,[],[f937,f103])).

fof(f103,plain,(
    v1_lattice3(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f937,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ v1_lattice3(sK11)
      | ~ v5_orders_2(sK11)
      | ~ v4_orders_2(sK11)
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(subsumption_resolution,[],[f936,f104])).

fof(f104,plain,(
    v2_lattice3(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f936,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ v2_lattice3(sK11)
      | ~ v1_lattice3(sK11)
      | ~ v5_orders_2(sK11)
      | ~ v4_orders_2(sK11)
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(subsumption_resolution,[],[f934,f105])).

fof(f934,plain,(
    ! [X43,X42] :
      ( ~ sP8(X42,X43,k7_lattice3(sK11))
      | ~ l1_orders_2(sK11)
      | ~ v2_lattice3(sK11)
      | ~ v1_lattice3(sK11)
      | ~ v5_orders_2(sK11)
      | ~ v4_orders_2(sK11)
      | ~ v3_orders_2(sK11)
      | ~ r1_subset_1(sK12,sK14(X42,X43,k7_lattice3(sK11)))
      | ~ r1_tarski(sK13,sK14(X42,X43,k7_lattice3(sK11))) ) ),
    inference(resolution,[],[f820,f715])).

fof(f715,plain,(
    ! [X0] :
      ( ~ sP9(sK11,X0)
      | ~ r1_subset_1(sK12,X0)
      | ~ r1_tarski(sK13,X0) ) ),
    inference(subsumption_resolution,[],[f714,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( sP9(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(X1,X0)
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_7(X1,X0)
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP9(X0,X1) ) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ( sP9(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_7(X1,X0)
        | ~ v13_waybel_0(X1,X0)
        | ~ v2_waybel_0(X1,X0)
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v2_waybel_7(X1,X0)
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
        | ~ sP9(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP9(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_7(X1,X0)
        & v13_waybel_0(X1,X0)
        & v2_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f714,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK13,X0)
      | ~ r1_subset_1(sK12,X0)
      | v1_xboole_0(X0)
      | ~ sP9(sK11,X0) ) ),
    inference(subsumption_resolution,[],[f713,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0,X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f713,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK13,X0)
      | ~ r1_subset_1(sK12,X0)
      | ~ v2_waybel_0(X0,sK11)
      | v1_xboole_0(X0)
      | ~ sP9(sK11,X0) ) ),
    inference(subsumption_resolution,[],[f712,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0,X1)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f712,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK13,X0)
      | ~ r1_subset_1(sK12,X0)
      | ~ v13_waybel_0(X0,sK11)
      | ~ v2_waybel_0(X0,sK11)
      | v1_xboole_0(X0)
      | ~ sP9(sK11,X0) ) ),
    inference(subsumption_resolution,[],[f706,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ sP9(X0,X1)
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f706,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK13,X0)
      | ~ v2_waybel_7(X0,sK11)
      | ~ r1_subset_1(sK12,X0)
      | ~ v13_waybel_0(X0,sK11)
      | ~ v2_waybel_0(X0,sK11)
      | v1_xboole_0(X0)
      | ~ sP9(sK11,X0) ) ),
    inference(resolution,[],[f115,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f115,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK11)))
      | ~ r1_tarski(sK13,X3)
      | ~ v2_waybel_7(X3,sK11)
      | ~ r1_subset_1(sK12,X3)
      | ~ v13_waybel_0(X3,sK11)
      | ~ v2_waybel_0(X3,sK11)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f820,plain,(
    ! [X2,X0,X1] :
      ( sP9(X2,sK14(X0,X1,k7_lattice3(X2)))
      | ~ sP8(X0,X1,k7_lattice3(X2))
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v1_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2) ) ),
    inference(resolution,[],[f819,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ sP10(X0,X1)
      | sP9(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP9(X0,X1)
            | ~ sP10(X0,X1) )
          & ( sP10(X0,X1)
            | ~ sP9(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP9(X0,X1)
        <=> sP10(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f36,f64,f63])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP10(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        & v1_waybel_7(X1,k7_lattice3(X0))
        & v12_waybel_0(X1,k7_lattice3(X0))
        & v1_waybel_0(X1,k7_lattice3(X0))
        & ~ v1_xboole_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_7(X1,X0)
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_7(X1,k7_lattice3(X0))
            & v12_waybel_0(X1,k7_lattice3(X0))
            & v1_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_7)).

fof(f819,plain,(
    ! [X21,X22,X20] :
      ( sP10(X20,sK14(X21,X22,k7_lattice3(X20)))
      | ~ sP8(X21,X22,k7_lattice3(X20)) ) ),
    inference(subsumption_resolution,[],[f818,f149])).

fof(f818,plain,(
    ! [X21,X22,X20] :
      ( sP10(X20,sK14(X21,X22,k7_lattice3(X20)))
      | v1_xboole_0(sK14(X21,X22,k7_lattice3(X20)))
      | ~ sP8(X21,X22,k7_lattice3(X20)) ) ),
    inference(subsumption_resolution,[],[f817,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK14(X0,X1,X2),X2)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f817,plain,(
    ! [X21,X22,X20] :
      ( sP10(X20,sK14(X21,X22,k7_lattice3(X20)))
      | ~ v1_waybel_0(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | v1_xboole_0(sK14(X21,X22,k7_lattice3(X20)))
      | ~ sP8(X21,X22,k7_lattice3(X20)) ) ),
    inference(subsumption_resolution,[],[f816,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK14(X0,X1,X2),X2)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f816,plain,(
    ! [X21,X22,X20] :
      ( sP10(X20,sK14(X21,X22,k7_lattice3(X20)))
      | ~ v12_waybel_0(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | ~ v1_waybel_0(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | v1_xboole_0(sK14(X21,X22,k7_lattice3(X20)))
      | ~ sP8(X21,X22,k7_lattice3(X20)) ) ),
    inference(subsumption_resolution,[],[f810,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK14(X0,X1,X2),X2)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f810,plain,(
    ! [X21,X22,X20] :
      ( sP10(X20,sK14(X21,X22,k7_lattice3(X20)))
      | ~ v1_waybel_7(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | ~ v12_waybel_0(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | ~ v1_waybel_0(sK14(X21,X22,k7_lattice3(X20)),k7_lattice3(X20))
      | v1_xboole_0(sK14(X21,X22,k7_lattice3(X20)))
      | ~ sP8(X21,X22,k7_lattice3(X20)) ) ),
    inference(resolution,[],[f163,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | sP10(X0,X1)
      | ~ v1_waybel_7(X1,k7_lattice3(X0))
      | ~ v12_waybel_0(X1,k7_lattice3(X0))
      | ~ v1_waybel_0(X1,k7_lattice3(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( sP10(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v1_waybel_7(X1,k7_lattice3(X0))
        | ~ v12_waybel_0(X1,k7_lattice3(X0))
        | ~ v1_waybel_0(X1,k7_lattice3(X0))
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v1_waybel_7(X1,k7_lattice3(X0))
          & v12_waybel_0(X1,k7_lattice3(X0))
          & v1_waybel_0(X1,k7_lattice3(X0))
          & ~ v1_xboole_0(X1) )
        | ~ sP10(X0,X1) ) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( sP10(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v1_waybel_7(X1,k7_lattice3(X0))
        | ~ v12_waybel_0(X1,k7_lattice3(X0))
        | ~ v1_waybel_0(X1,k7_lattice3(X0))
        | v1_xboole_0(X1) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v1_waybel_7(X1,k7_lattice3(X0))
          & v12_waybel_0(X1,k7_lattice3(X0))
          & v1_waybel_0(X1,k7_lattice3(X0))
          & ~ v1_xboole_0(X1) )
        | ~ sP10(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f1645,plain,(
    ! [X10,X11,X9] :
      ( sP8(X9,X10,X11)
      | ~ v13_waybel_0(X9,X11)
      | v1_xboole_0(X9)
      | ~ r1_subset_1(X10,X9)
      | ~ v1_waybel_0(X10,X11)
      | v1_xboole_0(X10)
      | ~ l1_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v2_waybel_1(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ sP7(X11,X9)
      | ~ sP2(X11,X10) ) ),
    inference(subsumption_resolution,[],[f1634,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1634,plain,(
    ! [X10,X11,X9] :
      ( sP8(X9,X10,X11)
      | ~ v13_waybel_0(X9,X11)
      | v1_xboole_0(X9)
      | ~ r1_subset_1(X10,X9)
      | ~ v12_waybel_0(X10,X11)
      | ~ v1_waybel_0(X10,X11)
      | v1_xboole_0(X10)
      | ~ l1_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ v1_lattice3(X11)
      | ~ v2_waybel_1(X11)
      | ~ v5_orders_2(X11)
      | ~ v4_orders_2(X11)
      | ~ v3_orders_2(X11)
      | ~ sP7(X11,X9)
      | ~ sP2(X11,X10) ) ),
    inference(resolution,[],[f1157,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1157,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5)))
      | sP8(X4,X3,X5)
      | ~ v13_waybel_0(X4,X5)
      | v1_xboole_0(X4)
      | ~ r1_subset_1(X3,X4)
      | ~ v12_waybel_0(X3,X5)
      | ~ v1_waybel_0(X3,X5)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v1_lattice3(X5)
      | ~ v2_waybel_1(X5)
      | ~ v5_orders_2(X5)
      | ~ v4_orders_2(X5)
      | ~ v3_orders_2(X5)
      | ~ sP7(X5,X4) ) ),
    inference(subsumption_resolution,[],[f1142,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ sP7(X0,X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1142,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_subset_1(X3,X4)
      | sP8(X4,X3,X5)
      | ~ v13_waybel_0(X4,X5)
      | ~ v2_waybel_0(X4,X5)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v12_waybel_0(X3,X5)
      | ~ v1_waybel_0(X3,X5)
      | v1_xboole_0(X3)
      | ~ l1_orders_2(X5)
      | ~ v2_lattice3(X5)
      | ~ v1_lattice3(X5)
      | ~ v2_waybel_1(X5)
      | ~ v5_orders_2(X5)
      | ~ v4_orders_2(X5)
      | ~ v3_orders_2(X5)
      | ~ sP7(X5,X4) ) ),
    inference(resolution,[],[f156,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | sP8(X2,X1,X0)
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP8(X2,X1,X0)
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f32,f61])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_waybel_7)).

fof(f1564,plain,(
    spl15_20 ),
    inference(avatar_contradiction_clause,[],[f1563])).

fof(f1563,plain,
    ( $false
    | spl15_20 ),
    inference(subsumption_resolution,[],[f1562,f333])).

fof(f333,plain,(
    sP6(sK11,sK13) ),
    inference(subsumption_resolution,[],[f331,f105])).

fof(f331,plain,
    ( sP6(sK11,sK13)
    | ~ l1_orders_2(sK11) ),
    inference(resolution,[],[f325,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ sP7(X0,X1)
      | sP6(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP6(X0,X1)
            | ~ sP7(X0,X1) )
          & ( sP7(X0,X1)
            | ~ sP6(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
        <=> sP7(X0,X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f30,f59,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP6(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        & v1_waybel_0(X1,k7_lattice3(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v1_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_7)).

fof(f325,plain,(
    sP7(sK11,sK13) ),
    inference(subsumption_resolution,[],[f305,f111])).

fof(f111,plain,(
    v2_waybel_0(sK13,sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f305,plain,
    ( sP7(sK11,sK13)
    | ~ v2_waybel_0(sK13,sK11) ),
    inference(resolution,[],[f143,f113])).

fof(f113,plain,(
    m1_subset_1(sK13,k1_zfmisc_1(u1_struct_0(sK11))) ),
    inference(cnf_transformation,[],[f69])).

fof(f1562,plain,
    ( ~ sP6(sK11,sK13)
    | spl15_20 ),
    inference(resolution,[],[f1458,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,k7_lattice3(X0))
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( sP6(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v1_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v1_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP6(X0,X1) ) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( sP6(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v1_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v1_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP6(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f1458,plain,
    ( ~ v1_waybel_0(sK13,k7_lattice3(sK11))
    | spl15_20 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1495,plain,(
    spl15_11 ),
    inference(avatar_contradiction_clause,[],[f1494])).

fof(f1494,plain,
    ( $false
    | spl15_11 ),
    inference(subsumption_resolution,[],[f1492,f290])).

fof(f290,plain,(
    sP4(sK11,sK13) ),
    inference(subsumption_resolution,[],[f288,f105])).

fof(f288,plain,
    ( sP4(sK11,sK13)
    | ~ l1_orders_2(sK11) ),
    inference(resolution,[],[f283,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | sP4(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP4(X0,X1)
            | ~ sP5(X0,X1) )
          & ( sP5(X0,X1)
            | ~ sP4(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
        <=> sP5(X0,X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f29,f56,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        & v12_waybel_0(X1,k7_lattice3(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v12_waybel_0(X1,k7_lattice3(X0)) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_7)).

fof(f283,plain,(
    sP5(sK11,sK13) ),
    inference(subsumption_resolution,[],[f263,f112])).

fof(f112,plain,(
    v13_waybel_0(sK13,sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f263,plain,
    ( sP5(sK11,sK13)
    | ~ v13_waybel_0(sK13,sK11) ),
    inference(resolution,[],[f135,f113])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X0,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
        | ~ sP5(X0,X1) ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
        | ~ sP5(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f1492,plain,
    ( ~ sP4(sK11,sK13)
    | spl15_11 ),
    inference(resolution,[],[f1422,f243])).

fof(f243,plain,(
    ! [X14,X15] :
      ( sP2(k7_lattice3(X14),X15)
      | ~ sP4(X14,X15) ) ),
    inference(subsumption_resolution,[],[f229,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,k7_lattice3(X0))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v12_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v12_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
        | ~ v12_waybel_0(X1,k7_lattice3(X0)) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          & v12_waybel_0(X1,k7_lattice3(X0)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f229,plain,(
    ! [X14,X15] :
      ( sP2(k7_lattice3(X14),X15)
      | ~ v12_waybel_0(X15,k7_lattice3(X14))
      | ~ sP4(X14,X15) ) ),
    inference(resolution,[],[f130,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f1422,plain,
    ( ~ sP2(k7_lattice3(sK11),sK13)
    | spl15_11 ),
    inference(avatar_component_clause,[],[f1420])).

fof(f1491,plain,(
    spl15_19 ),
    inference(avatar_contradiction_clause,[],[f1490])).

fof(f1490,plain,
    ( $false
    | spl15_19 ),
    inference(subsumption_resolution,[],[f1489,f105])).

fof(f1489,plain,
    ( ~ l1_orders_2(sK11)
    | spl15_19 ),
    inference(resolution,[],[f1454,f116])).

fof(f116,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f1454,plain,
    ( ~ l1_orders_2(k7_lattice3(sK11))
    | spl15_19 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1488,plain,(
    spl15_18 ),
    inference(avatar_contradiction_clause,[],[f1487])).

fof(f1487,plain,
    ( $false
    | spl15_18 ),
    inference(subsumption_resolution,[],[f1486,f103])).

fof(f1486,plain,
    ( ~ v1_lattice3(sK11)
    | spl15_18 ),
    inference(subsumption_resolution,[],[f1485,f105])).

fof(f1485,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v1_lattice3(sK11)
    | spl15_18 ),
    inference(resolution,[],[f1450,f172])).

fof(f172,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => v2_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0) )
     => ( v2_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_7)).

fof(f1450,plain,
    ( ~ v2_lattice3(k7_lattice3(sK11))
    | spl15_18 ),
    inference(avatar_component_clause,[],[f1448])).

fof(f1484,plain,(
    spl15_17 ),
    inference(avatar_contradiction_clause,[],[f1483])).

fof(f1483,plain,
    ( $false
    | spl15_17 ),
    inference(subsumption_resolution,[],[f1482,f104])).

fof(f1482,plain,
    ( ~ v2_lattice3(sK11)
    | spl15_17 ),
    inference(subsumption_resolution,[],[f1481,f105])).

fof(f1481,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v2_lattice3(sK11)
    | spl15_17 ),
    inference(resolution,[],[f1446,f173])).

fof(f173,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => v1_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(f1446,plain,
    ( ~ v1_lattice3(k7_lattice3(sK11))
    | spl15_17 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1480,plain,(
    spl15_16 ),
    inference(avatar_contradiction_clause,[],[f1479])).

fof(f1479,plain,
    ( $false
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1478,f99])).

fof(f1478,plain,
    ( ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1477,f100])).

fof(f1477,plain,
    ( ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1476,f101])).

fof(f1476,plain,
    ( ~ v5_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1475,f103])).

fof(f1475,plain,
    ( ~ v1_lattice3(sK11)
    | ~ v5_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1474,f104])).

fof(f1474,plain,
    ( ~ v2_lattice3(sK11)
    | ~ v1_lattice3(sK11)
    | ~ v5_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1473,f102])).

fof(f102,plain,(
    v2_waybel_1(sK11) ),
    inference(cnf_transformation,[],[f69])).

fof(f1473,plain,
    ( ~ v2_waybel_1(sK11)
    | ~ v2_lattice3(sK11)
    | ~ v1_lattice3(sK11)
    | ~ v5_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(subsumption_resolution,[],[f1472,f105])).

fof(f1472,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v2_waybel_1(sK11)
    | ~ v2_lattice3(sK11)
    | ~ v1_lattice3(sK11)
    | ~ v5_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_16 ),
    inference(resolution,[],[f1442,f157])).

fof(f157,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_waybel_1(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_1(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_waybel_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v2_waybel_1(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_yellow_7)).

fof(f1442,plain,
    ( ~ v2_waybel_1(k7_lattice3(sK11))
    | spl15_16 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f1471,plain,(
    spl15_15 ),
    inference(avatar_contradiction_clause,[],[f1470])).

fof(f1470,plain,
    ( $false
    | spl15_15 ),
    inference(subsumption_resolution,[],[f1469,f101])).

fof(f1469,plain,
    ( ~ v5_orders_2(sK11)
    | spl15_15 ),
    inference(subsumption_resolution,[],[f1468,f105])).

fof(f1468,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v5_orders_2(sK11)
    | spl15_15 ),
    inference(resolution,[],[f1438,f174])).

fof(f174,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => v5_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(f1438,plain,
    ( ~ v5_orders_2(k7_lattice3(sK11))
    | spl15_15 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1467,plain,(
    spl15_14 ),
    inference(avatar_contradiction_clause,[],[f1466])).

fof(f1466,plain,
    ( $false
    | spl15_14 ),
    inference(subsumption_resolution,[],[f1465,f100])).

fof(f1465,plain,
    ( ~ v4_orders_2(sK11)
    | spl15_14 ),
    inference(subsumption_resolution,[],[f1464,f105])).

fof(f1464,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v4_orders_2(sK11)
    | spl15_14 ),
    inference(resolution,[],[f1434,f175])).

fof(f175,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => v4_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(f1434,plain,
    ( ~ v4_orders_2(k7_lattice3(sK11))
    | spl15_14 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1463,plain,(
    spl15_13 ),
    inference(avatar_contradiction_clause,[],[f1462])).

fof(f1462,plain,
    ( $false
    | spl15_13 ),
    inference(subsumption_resolution,[],[f1461,f99])).

fof(f1461,plain,
    ( ~ v3_orders_2(sK11)
    | spl15_13 ),
    inference(subsumption_resolution,[],[f1460,f105])).

fof(f1460,plain,
    ( ~ l1_orders_2(sK11)
    | ~ v3_orders_2(sK11)
    | spl15_13 ),
    inference(resolution,[],[f1430,f176])).

fof(f176,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v3_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(f1430,plain,
    ( ~ v3_orders_2(k7_lattice3(sK11))
    | spl15_13 ),
    inference(avatar_component_clause,[],[f1428])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1263+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  197 (1931 expanded)
%              Number of leaves         :   39 ( 586 expanded)
%              Depth                    :   23
%              Number of atoms          :  834 (15658 expanded)
%              Number of equality atoms :   55 (2305 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f973,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f135,f199,f211,f220,f229,f238,f244,f445,f713,f763,f798,f972])).

fof(f972,plain,
    ( spl7_4
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | spl7_4
    | ~ spl7_5
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f970,f243])).

fof(f243,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl7_13
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f970,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f739,f794,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f106_D])).

fof(f106_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f794,plain,
    ( ~ sP6(sK2)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f783,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f103,f106_D])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f783,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f88,f780,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f780,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f125,plain,
    ( k1_xboole_0 != sK2
    | spl7_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f739,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f130,f148])).

fof(f148,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f136,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f136,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ( r1_xboole_0(sK1,sK2)
        & v3_pre_topc(sK2,sK0)
        & k1_xboole_0 != sK2
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v1_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( ~ r1_xboole_0(sK1,X3)
          | ~ v3_pre_topc(X3,sK0)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v1_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v1_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,sK0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v1_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,sK0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v1_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( r1_xboole_0(X1,X2)
              & v3_pre_topc(X2,sK0)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v1_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( ~ r1_xboole_0(X1,X3)
              | ~ v3_pre_topc(X3,sK0)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v1_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( r1_xboole_0(sK1,X2)
            & v3_pre_topc(X2,sK0)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v1_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( ~ r1_xboole_0(sK1,X3)
            | ~ v3_pre_topc(X3,sK0)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v1_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( r1_xboole_0(sK1,X2)
        & v3_pre_topc(X2,sK0)
        & k1_xboole_0 != X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r1_xboole_0(sK1,sK2)
      & v3_pre_topc(sK2,sK0)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f798,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f789,f796])).

fof(f796,plain,
    ( ~ r2_hidden(sK4(sK2),k2_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f795,f723])).

fof(f723,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f722])).

fof(f722,plain,
    ( spl7_20
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f795,plain,
    ( ~ r2_hidden(sK4(sK2),k2_pre_topc(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f120,f115,f146,f739,f783,f190])).

fof(f190,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | ~ r2_hidden(X4,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(X4,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl7_8
  <=> ! [X3,X2,X4] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X4,k2_pre_topc(sK0,X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(X4,X3)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f146,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f145,f136])).

fof(f145,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f69,f76])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f120,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f789,plain,
    ( r2_hidden(sK4(sK2),k2_struct_0(sK0))
    | spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f787,f783,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f787,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f739,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f763,plain,
    ( spl7_20
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f760,f109,f722])).

fof(f109,plain,
    ( spl7_1
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f760,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f146,f110,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f160,f68])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f79,f148])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f110,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f713,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f75,f632])).

fof(f632,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f631,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f631,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
        | ~ v1_xboole_0(X0) )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(superposition,[],[f609,f81])).

fof(f609,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_xboole_0)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f562,f601])).

fof(f601,plain,
    ( k1_xboole_0 = sK3(sK0,sK1,sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | spl7_1
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f561,f563,f560,f150])).

fof(f150,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f134,f148])).

fof(f134,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_6
  <=> ! [X3] :
        ( ~ r1_xboole_0(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f560,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl7_1
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f146,f392,f442,f204])).

fof(f204,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(X12,k2_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(sK3(sK0,X11,X12),k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X12,k2_pre_topc(sK0,X11)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_9
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X12,k2_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X11,X12),k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X12,k2_pre_topc(sK0,X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f442,plain,
    ( m1_subset_1(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k2_struct_0(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f156,f391,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f391,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k2_struct_0(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f381,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f381,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f140,f251,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f251,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f154,f99])).

fof(f154,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f142,f148])).

fof(f142,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f69,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f140,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f68,f111,f69,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f156,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f147,f148])).

fof(f147,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f136,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f392,plain,
    ( ~ r2_hidden(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f381,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f563,plain,
    ( r1_xboole_0(sK1,sK3(sK0,sK1,sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | spl7_1
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f146,f392,f442,f234])).

fof(f234,plain,
    ( ! [X26,X25] :
        ( r1_xboole_0(X25,sK3(sK0,X25,X26))
        | ~ m1_subset_1(X26,k2_struct_0(sK0))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X26,k2_pre_topc(sK0,X25)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_12
  <=> ! [X25,X26] :
        ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X26,k2_struct_0(sK0))
        | r1_xboole_0(X25,sK3(sK0,X25,X26))
        | r2_hidden(X26,k2_pre_topc(sK0,X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f561,plain,
    ( v3_pre_topc(sK3(sK0,sK1,sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),sK0)
    | spl7_1
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f146,f392,f442,f216])).

fof(f216,plain,
    ( ! [X17,X18] :
        ( v3_pre_topc(sK3(sK0,X17,X18),sK0)
        | ~ m1_subset_1(X18,k2_struct_0(sK0))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X18,k2_pre_topc(sK0,X17)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl7_10
  <=> ! [X18,X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X18,k2_struct_0(sK0))
        | v3_pre_topc(sK3(sK0,X17,X18),sK0)
        | r2_hidden(X18,k2_pre_topc(sK0,X17)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f562,plain,
    ( r2_hidden(sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK3(sK0,sK1,sK5(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | spl7_1
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f146,f392,f442,f225])).

fof(f225,plain,
    ( ! [X21,X22] :
        ( ~ m1_subset_1(X22,k2_struct_0(sK0))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X22,sK3(sK0,X21,X22))
        | r2_hidden(X22,k2_pre_topc(sK0,X21)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl7_11
  <=> ! [X22,X21] :
        ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X22,k2_struct_0(sK0))
        | r2_hidden(X22,sK3(sK0,X21,X22))
        | r2_hidden(X22,k2_pre_topc(sK0,X21)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f75,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f445,plain,
    ( ~ spl7_13
    | spl7_1 ),
    inference(avatar_split_clause,[],[f441,f109,f241])).

fof(f441,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f391,f101])).

fof(f244,plain,
    ( ~ spl7_7
    | spl7_13 ),
    inference(avatar_split_clause,[],[f239,f241,f185])).

fof(f185,plain,
    ( spl7_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f239,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f136])).

fof(f174,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(superposition,[],[f87,f148])).

fof(f87,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f238,plain,
    ( spl7_7
    | spl7_12 ),
    inference(avatar_split_clause,[],[f237,f233,f185])).

fof(f237,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | r2_hidden(X27,k2_pre_topc(sK0,X28))
      | r1_xboole_0(X28,sK3(sK0,X28,X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f67])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f236,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | r2_hidden(X27,k2_pre_topc(sK0,X28))
      | r1_xboole_0(X28,sK3(sK0,X28,X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f68])).

fof(f173,plain,(
    ! [X28,X27] :
      ( ~ m1_subset_1(X27,k2_struct_0(sK0))
      | r2_hidden(X27,k2_pre_topc(sK0,X28))
      | r1_xboole_0(X28,sK3(sK0,X28,X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f86,f148])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK3(X0,X1,X2))
                    & r2_hidden(X2,sK3(X0,X1,X2))
                    & v3_pre_topc(sK3(X0,X1,X2),X0)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK3(X0,X1,X2))
        & r2_hidden(X2,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(f229,plain,
    ( spl7_7
    | spl7_11 ),
    inference(avatar_split_clause,[],[f228,f224,f185])).

fof(f228,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(X23,k2_struct_0(sK0))
      | r2_hidden(X23,k2_pre_topc(sK0,X24))
      | r2_hidden(X23,sK3(sK0,X24,X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f227,f67])).

fof(f227,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(X23,k2_struct_0(sK0))
      | r2_hidden(X23,k2_pre_topc(sK0,X24))
      | r2_hidden(X23,sK3(sK0,X24,X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f68])).

fof(f171,plain,(
    ! [X24,X23] :
      ( ~ m1_subset_1(X23,k2_struct_0(sK0))
      | r2_hidden(X23,k2_pre_topc(sK0,X24))
      | r2_hidden(X23,sK3(sK0,X24,X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f85,f148])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f220,plain,
    ( spl7_7
    | spl7_10 ),
    inference(avatar_split_clause,[],[f219,f215,f185])).

fof(f219,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,k2_struct_0(sK0))
      | r2_hidden(X19,k2_pre_topc(sK0,X20))
      | v3_pre_topc(sK3(sK0,X20,X19),sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f67])).

fof(f218,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,k2_struct_0(sK0))
      | r2_hidden(X19,k2_pre_topc(sK0,X20))
      | v3_pre_topc(sK3(sK0,X20,X19),sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,k2_struct_0(sK0))
      | r2_hidden(X19,k2_pre_topc(sK0,X20))
      | v3_pre_topc(sK3(sK0,X20,X19),sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f84,f148])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f211,plain,
    ( spl7_7
    | spl7_9 ),
    inference(avatar_split_clause,[],[f210,f203,f185])).

fof(f210,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK3(sK0,X15,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,k2_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209,f67])).

fof(f209,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK3(sK0,X15,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,k2_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f68])).

fof(f167,plain,(
    ! [X15,X16] :
      ( m1_subset_1(sK3(sK0,X15,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X16,k2_pre_topc(sK0,X15))
      | ~ m1_subset_1(X16,k2_struct_0(sK0))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f83,f148])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f199,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f198,f189,f185])).

fof(f198,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_xboole_0(X9,X8)
      | ~ r2_hidden(X10,X8)
      | ~ v3_pre_topc(X8,sK0)
      | ~ r2_hidden(X10,k2_pre_topc(sK0,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f102])).

fof(f197,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_xboole_0(X9,X8)
      | ~ r2_hidden(X10,X8)
      | ~ v3_pre_topc(X8,sK0)
      | ~ r2_hidden(X10,k2_pre_topc(sK0,X9))
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f67])).

fof(f196,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_xboole_0(X9,X8)
      | ~ r2_hidden(X10,X8)
      | ~ v3_pre_topc(X8,sK0)
      | ~ r2_hidden(X10,k2_pre_topc(sK0,X9))
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f68])).

fof(f164,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_xboole_0(X9,X8)
      | ~ r2_hidden(X10,X8)
      | ~ v3_pre_topc(X8,sK0)
      | ~ r2_hidden(X10,k2_pre_topc(sK0,X9))
      | ~ m1_subset_1(X10,k2_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f82,f148])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f135,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f70,f133,f109])).

fof(f70,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK1,X3)
      | ~ v3_pre_topc(X3,sK0)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f71,f128,f109])).

fof(f71,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f72,f123,f109])).

fof(f72,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f73,f118,f109])).

fof(f73,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f74,f113,f109])).

fof(f74,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------

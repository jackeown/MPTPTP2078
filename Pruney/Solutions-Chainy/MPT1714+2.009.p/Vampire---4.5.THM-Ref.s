%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:54 EST 2020

% Result     : Theorem 3.58s
% Output     : Refutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  283 (4409 expanded)
%              Number of leaves         :   33 (1686 expanded)
%              Depth                    :   33
%              Number of atoms          : 1091 (47315 expanded)
%              Number of equality atoms :  104 ( 646 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4076,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f131,f1761,f2503,f2847,f2850,f2920,f3831,f4057,f4063,f4073])).

fof(f4073,plain,
    ( ~ spl11_4
    | spl11_66
    | ~ spl11_87
    | ~ spl11_89
    | ~ spl11_104 ),
    inference(avatar_contradiction_clause,[],[f4072])).

fof(f4072,plain,
    ( $false
    | ~ spl11_4
    | spl11_66
    | ~ spl11_87
    | ~ spl11_89
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f4055,f4067])).

fof(f4067,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | spl11_66
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f4066,f1760])).

fof(f1760,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | spl11_66 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1758,plain,
    ( spl11_66
  <=> r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f4066,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f3663,f142])).

fof(f142,plain,(
    l1_struct_0(sK8) ),
    inference(resolution,[],[f139,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f139,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f63,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
    & ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(sK6,X3) )
              & m1_pre_topc(sK6,X2)
              & m1_pre_topc(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK5)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(sK6,X3) )
            & m1_pre_topc(sK6,X2)
            & m1_pre_topc(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK7)
            | r1_tsep_1(sK7,X3) )
          & ( ~ r1_tsep_1(X3,sK6)
            | ~ r1_tsep_1(sK6,X3) )
          & m1_pre_topc(sK6,sK7)
          & m1_pre_topc(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK7)
          | r1_tsep_1(sK7,X3) )
        & ( ~ r1_tsep_1(X3,sK6)
          | ~ r1_tsep_1(sK6,X3) )
        & m1_pre_topc(sK6,sK7)
        & m1_pre_topc(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ( r1_tsep_1(sK8,sK7)
        | r1_tsep_1(sK7,sK8) )
      & ( ~ r1_tsep_1(sK8,sK6)
        | ~ r1_tsep_1(sK6,sK8) )
      & m1_pre_topc(sK6,sK7)
      & m1_pre_topc(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
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
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
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
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f135,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f92,f69])).

fof(f69,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3663,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ l1_struct_0(sK8)
    | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(superposition,[],[f3633,f145])).

fof(f145,plain,(
    k2_struct_0(sK8) = u1_struct_0(sK8) ),
    inference(resolution,[],[f142,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3633,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
        | ~ l1_struct_0(X0)
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(duplicate_literal_removal,[],[f3624])).

fof(f3624,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))
        | ~ l1_struct_0(X0) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(resolution,[],[f3547,f3078])).

fof(f3078,plain,
    ( ! [X1] :
        ( ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
        | ~ l1_struct_0(X1) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2971,f2527])).

fof(f2527,plain,
    ( l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
    | ~ spl11_104 ),
    inference(resolution,[],[f2526,f76])).

fof(f2526,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK6,sK6))
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2511,f138])).

fof(f138,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f134,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f2511,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK6,sK6))
    | ~ l1_pre_topc(sK7)
    | ~ spl11_104 ),
    inference(resolution,[],[f2493,f92])).

fof(f2493,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)
    | ~ spl11_104 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f2492,plain,
    ( spl11_104
  <=> m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f2971,plain,
    ( ! [X1] :
        ( r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
        | ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) )
    | ~ spl11_87 ),
    inference(backward_demodulation,[],[f2400,f2200])).

fof(f2200,plain,
    ( k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))
    | ~ spl11_87 ),
    inference(avatar_component_clause,[],[f2198])).

fof(f2198,plain,
    ( spl11_87
  <=> k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f2400,plain,(
    ! [X1] :
      ( r1_xboole_0(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),u1_struct_0(X1))
      | ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ) ),
    inference(superposition,[],[f74,f2392])).

fof(f2392,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2391,f2162])).

fof(f2162,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2161,f921])).

fof(f921,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f917,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f917,plain,
    ( v2_struct_0(sK6)
    | k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    inference(resolution,[],[f901,f65])).

fof(f65,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f901,plain,(
    ! [X8] :
      ( ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8)) ) ),
    inference(subsumption_resolution,[],[f900,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f900,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8)) ) ),
    inference(subsumption_resolution,[],[f899,f63])).

fof(f899,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK5)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8)) ) ),
    inference(subsumption_resolution,[],[f885,f64])).

fof(f885,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8)) ) ),
    inference(resolution,[],[f675,f65])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f674])).

fof(f674,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0)) ) ),
    inference(resolution,[],[f108,f449])).

fof(f449,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(k1_tsep_1(X0,X2,X1)) = u1_struct_0(k1_tsep_1(X0,X2,X1)) ) ),
    inference(resolution,[],[f448,f73])).

fof(f448,plain,(
    ! [X2,X0,X1] :
      ( l1_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ l1_pre_topc(X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f165,f76])).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( l1_pre_topc(k1_tsep_1(X3,X5,X4))
      | ~ sP4(X3,X4,X5)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f107,f92])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f30,f36])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f2161,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2160,f143])).

fof(f143,plain,(
    k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(resolution,[],[f140,f73])).

fof(f140,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f137,f76])).

fof(f137,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f133,f63])).

fof(f133,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f92,f65])).

fof(f2160,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2156,f64])).

fof(f2156,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2075,f65])).

fof(f2075,plain,(
    ! [X8] :
      ( ~ m1_pre_topc(X8,sK5)
      | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6))
      | v2_struct_0(X8) ) ),
    inference(forward_demodulation,[],[f2074,f143])).

fof(f2074,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f2073,f61])).

fof(f2073,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f2072,f63])).

fof(f2072,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f2057,f64])).

fof(f2057,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f1526,f65])).

fof(f1526,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1525,f108])).

fof(f1525,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP4(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f1524,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1524,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | v2_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP4(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f1523,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1523,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ v1_pre_topc(k1_tsep_1(X2,X0,X1))
      | v2_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP4(X2,X1,X0) ) ),
    inference(resolution,[],[f110,f107])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f2391,plain,(
    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2390,f143])).

fof(f2390,plain,(
    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2387,f64])).

fof(f2387,plain,
    ( k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2090,f70])).

fof(f70,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f2090,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(X12,sK7)
      | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6))
      | v2_struct_0(X12) ) ),
    inference(forward_demodulation,[],[f2089,f143])).

fof(f2089,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f2088,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f2088,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f2087,f138])).

fof(f2087,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f2061,f64])).

fof(f2061,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f1526,f70])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f3547,plain,
    ( ! [X1] :
        ( r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(X1)
        | ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f3545,f2527])).

fof(f3545,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
        | ~ l1_struct_0(X1)
        | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(duplicate_literal_removal,[],[f3538])).

fof(f3538,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
        | ~ l1_struct_0(X1)
        | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(X1) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(resolution,[],[f3081,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f3081,plain,
    ( ! [X4] :
        ( r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
        | ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6))
        | ~ l1_struct_0(X4) )
    | ~ spl11_87
    | ~ spl11_104 ),
    inference(subsumption_resolution,[],[f2974,f2527])).

fof(f2974,plain,
    ( ! [X4] :
        ( ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6))
        | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(X4) )
    | ~ spl11_87 ),
    inference(backward_demodulation,[],[f2403,f2200])).

fof(f2403,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(k1_tsep_1(sK5,sK6,sK6)))
      | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
      | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
      | ~ l1_struct_0(X4) ) ),
    inference(superposition,[],[f75,f2392])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4055,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ spl11_4
    | ~ spl11_89 ),
    inference(resolution,[],[f3879,f1513])).

fof(f1513,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1359,f130])).

fof(f130,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl11_4
  <=> r1_tsep_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1359,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ r1_tsep_1(sK8,sK7) ),
    inference(subsumption_resolution,[],[f389,f142])).

fof(f389,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK8) ),
    inference(superposition,[],[f186,f145])).

fof(f186,plain,(
    ! [X2] :
      ( r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK7))
      | ~ r1_tsep_1(X2,sK7)
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f178,f141])).

fof(f141,plain,(
    l1_struct_0(sK7) ),
    inference(resolution,[],[f138,f76])).

fof(f178,plain,(
    ! [X2] :
      ( r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK7))
      | ~ r1_tsep_1(X2,sK7)
      | ~ l1_struct_0(sK7)
      | ~ l1_struct_0(X2) ) ),
    inference(superposition,[],[f74,f144])).

fof(f144,plain,(
    k2_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(resolution,[],[f141,f73])).

fof(f3879,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k2_struct_0(sK7))
        | r1_xboole_0(X1,k2_struct_0(sK6)) )
    | ~ spl11_89 ),
    inference(backward_demodulation,[],[f2180,f2222])).

fof(f2222,plain,
    ( k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ spl11_89 ),
    inference(avatar_component_clause,[],[f2220])).

fof(f2220,plain,
    ( spl11_89
  <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f2180,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK5,sK7,sK6)))
      | r1_xboole_0(X1,k2_struct_0(sK6)) ) ),
    inference(superposition,[],[f104,f2165])).

fof(f2165,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2164,f1106])).

fof(f1106,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f1102,f64])).

fof(f1102,plain,
    ( v2_struct_0(sK6)
    | k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(resolution,[],[f904,f65])).

fof(f904,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(X9)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f903,f61])).

fof(f903,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f902,f63])).

fof(f902,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f886,f66])).

fof(f886,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(resolution,[],[f675,f67])).

fof(f2164,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2163,f144])).

fof(f2163,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2157,f66])).

fof(f2157,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f2075,f67])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4063,plain,
    ( ~ spl11_3
    | spl11_4 ),
    inference(avatar_contradiction_clause,[],[f4062])).

fof(f4062,plain,
    ( $false
    | ~ spl11_3
    | spl11_4 ),
    inference(subsumption_resolution,[],[f162,f129])).

fof(f129,plain,
    ( ~ r1_tsep_1(sK8,sK7)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f162,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f161,f141])).

fof(f161,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f160,f142])).

fof(f160,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK7)
    | ~ spl11_3 ),
    inference(resolution,[],[f98,f126])).

fof(f126,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_3
  <=> r1_tsep_1(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f4057,plain,
    ( spl11_2
    | ~ spl11_4
    | ~ spl11_89 ),
    inference(avatar_contradiction_clause,[],[f4056])).

fof(f4056,plain,
    ( $false
    | spl11_2
    | ~ spl11_4
    | ~ spl11_89 ),
    inference(subsumption_resolution,[],[f4055,f427])).

fof(f427,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | spl11_2 ),
    inference(subsumption_resolution,[],[f426,f140])).

fof(f426,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f422,f121])).

fof(f121,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl11_2
  <=> r1_tsep_1(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f422,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | r1_tsep_1(sK8,sK6)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f320,f143])).

fof(f320,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f311,f142])).

fof(f311,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK8) ) ),
    inference(superposition,[],[f75,f145])).

fof(f3831,plain,(
    spl11_75 ),
    inference(avatar_contradiction_clause,[],[f3830])).

fof(f3830,plain,
    ( $false
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3829,f138])).

fof(f3829,plain,
    ( ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3828,f66])).

fof(f3828,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3827,f545])).

fof(f545,plain,(
    m1_pre_topc(sK7,sK7) ),
    inference(subsumption_resolution,[],[f544,f62])).

fof(f62,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f544,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f538,f63])).

fof(f538,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f536,f67])).

fof(f536,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f527])).

fof(f527,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f95,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f3827,plain,
    ( ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3826,f64])).

fof(f3826,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3825,f70])).

fof(f3825,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(duplicate_literal_removal,[],[f3824])).

fof(f3824,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_75 ),
    inference(resolution,[],[f3823,f108])).

fof(f3823,plain,
    ( ~ sP4(sK7,sK6,sK7)
    | spl11_75 ),
    inference(subsumption_resolution,[],[f3822,f138])).

fof(f3822,plain,
    ( ~ sP4(sK7,sK6,sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_75 ),
    inference(resolution,[],[f3807,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( sP2(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f107,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP2(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f146,f92])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP2(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f34,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & r2_hidden(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> sP0(X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( ! [X2] :
            ( sP1(X0,X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP2(X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f3807,plain,
    ( ~ sP2(k1_tsep_1(sK7,sK7,sK6),sK7)
    | spl11_75 ),
    inference(resolution,[],[f3785,f2034])).

fof(f2034,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | spl11_75 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f2033,plain,
    ( spl11_75
  <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).

fof(f3785,plain,(
    ! [X0] :
      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0))
      | ~ sP2(k1_tsep_1(sK7,sK7,sK6),X0) ) ),
    inference(superposition,[],[f79,f3773])).

fof(f3773,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f3772,f2395])).

fof(f2395,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f2394,f2165])).

fof(f2394,plain,(
    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f2393,f144])).

fof(f2393,plain,(
    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f2388,f66])).

fof(f2388,plain,
    ( k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f2090,f545])).

fof(f3772,plain,(
    u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f3767,f64])).

fof(f3767,plain,
    ( v2_struct_0(sK6)
    | u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(resolution,[],[f914,f70])).

fof(f914,plain,(
    ! [X13] :
      ( ~ m1_pre_topc(X13,sK7)
      | v2_struct_0(X13)
      | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13)) ) ),
    inference(subsumption_resolution,[],[f913,f138])).

fof(f913,plain,(
    ! [X13] :
      ( v2_struct_0(X13)
      | ~ m1_pre_topc(X13,sK7)
      | ~ l1_pre_topc(sK7)
      | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13)) ) ),
    inference(subsumption_resolution,[],[f893,f66])).

fof(f893,plain,(
    ! [X13] :
      ( v2_struct_0(X13)
      | ~ m1_pre_topc(X13,sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(sK7)
      | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13)) ) ),
    inference(duplicate_literal_removal,[],[f890])).

fof(f890,plain,(
    ! [X13] :
      ( v2_struct_0(X13)
      | ~ m1_pre_topc(X13,sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7)
      | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13)) ) ),
    inference(resolution,[],[f675,f545])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ sP1(X1,X0,sK9(X0,X1))
          & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP1(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ sP1(X1,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP1(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ~ sP1(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f2920,plain,(
    spl11_108 ),
    inference(avatar_contradiction_clause,[],[f2919])).

fof(f2919,plain,
    ( $false
    | spl11_108 ),
    inference(subsumption_resolution,[],[f2918,f137])).

fof(f2918,plain,
    ( ~ l1_pre_topc(sK6)
    | spl11_108 ),
    inference(subsumption_resolution,[],[f2917,f64])).

fof(f2917,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_108 ),
    inference(subsumption_resolution,[],[f2916,f543])).

fof(f543,plain,(
    m1_pre_topc(sK6,sK6) ),
    inference(subsumption_resolution,[],[f542,f62])).

fof(f542,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f537,f63])).

fof(f537,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f536,f65])).

fof(f2916,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_108 ),
    inference(duplicate_literal_removal,[],[f2915])).

fof(f2915,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_108 ),
    inference(resolution,[],[f2914,f108])).

fof(f2914,plain,
    ( ~ sP4(sK6,sK6,sK6)
    | spl11_108 ),
    inference(subsumption_resolution,[],[f2913,f137])).

fof(f2913,plain,
    ( ~ sP4(sK6,sK6,sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_108 ),
    inference(resolution,[],[f2906,f164])).

fof(f2906,plain,
    ( ~ sP2(k1_tsep_1(sK6,sK6,sK6),sK6)
    | spl11_108 ),
    inference(resolution,[],[f2895,f2846])).

fof(f2846,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))
    | spl11_108 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f2844,plain,
    ( spl11_108
  <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).

fof(f2895,plain,(
    ! [X0] :
      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(X0))
      | ~ sP2(k1_tsep_1(sK6,sK6,sK6),X0) ) ),
    inference(superposition,[],[f79,f2889])).

fof(f2889,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2888,f2589])).

fof(f2589,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2588,f2162])).

fof(f2588,plain,(
    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2587,f143])).

fof(f2587,plain,(
    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2585,f64])).

fof(f2585,plain,
    ( k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2086,f543])).

fof(f2086,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK6)
      | u1_struct_0(k1_tsep_1(sK6,X11,sK6)) = k2_xboole_0(u1_struct_0(X11),k2_struct_0(sK6))
      | v2_struct_0(X11) ) ),
    inference(forward_demodulation,[],[f2085,f143])).

fof(f2085,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f2084,f137])).

fof(f2084,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6) ) ),
    inference(subsumption_resolution,[],[f2067,f64])).

fof(f2067,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6) ) ),
    inference(duplicate_literal_removal,[],[f2060])).

fof(f2060,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f1526,f543])).

fof(f2888,plain,(
    u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2886,f64])).

fof(f2886,plain,
    ( v2_struct_0(sK6)
    | u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(resolution,[],[f909,f543])).

fof(f909,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11)) ) ),
    inference(subsumption_resolution,[],[f908,f137])).

fof(f908,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK6)
      | ~ l1_pre_topc(sK6)
      | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11)) ) ),
    inference(subsumption_resolution,[],[f894,f64])).

fof(f894,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK6)
      | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11)) ) ),
    inference(duplicate_literal_removal,[],[f888])).

fof(f888,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(sK6)
      | ~ l1_pre_topc(sK6)
      | v2_struct_0(sK6)
      | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11)) ) ),
    inference(resolution,[],[f675,f543])).

fof(f2850,plain,
    ( spl11_89
    | ~ spl11_75 ),
    inference(avatar_split_clause,[],[f2179,f2033,f2220])).

fof(f2179,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(superposition,[],[f158,f2165])).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f101,f97])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2847,plain,
    ( spl11_87
    | ~ spl11_108 ),
    inference(avatar_split_clause,[],[f2171,f2844,f2198])).

fof(f2171,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))
    | k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    inference(superposition,[],[f158,f2162])).

fof(f2503,plain,(
    spl11_104 ),
    inference(avatar_contradiction_clause,[],[f2502])).

fof(f2502,plain,
    ( $false
    | spl11_104 ),
    inference(subsumption_resolution,[],[f2501,f66])).

fof(f2501,plain,
    ( v2_struct_0(sK7)
    | spl11_104 ),
    inference(subsumption_resolution,[],[f2500,f138])).

fof(f2500,plain,
    ( ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_104 ),
    inference(subsumption_resolution,[],[f2499,f64])).

fof(f2499,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_104 ),
    inference(subsumption_resolution,[],[f2498,f70])).

fof(f2498,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_104 ),
    inference(duplicate_literal_removal,[],[f2497])).

fof(f2497,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_104 ),
    inference(resolution,[],[f2496,f108])).

fof(f2496,plain,
    ( ~ sP4(sK7,sK6,sK6)
    | spl11_104 ),
    inference(resolution,[],[f2494,f107])).

fof(f2494,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)
    | spl11_104 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f1761,plain,
    ( spl11_1
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f1354,f1758,f115])).

fof(f115,plain,
    ( spl11_1
  <=> r1_tsep_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1354,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | r1_tsep_1(sK6,sK8) ),
    inference(subsumption_resolution,[],[f444,f140])).

fof(f444,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f324,f143])).

fof(f324,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK8))
      | r1_tsep_1(X3,sK8)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f315,f142])).

fof(f315,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK8))
      | r1_tsep_1(X3,sK8)
      | ~ l1_struct_0(sK8)
      | ~ l1_struct_0(X3) ) ),
    inference(superposition,[],[f75,f145])).

fof(f131,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f72,f128,f124])).

fof(f72,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f71,f119,f115])).

fof(f71,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:29:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (14236)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14240)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (14238)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (14247)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14248)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (14252)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14256)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (14243)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (14235)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (14242)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (14259)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (14245)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (14250)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (14237)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (14235)Refutation not found, incomplete strategy% (14235)------------------------------
% 0.21/0.53  % (14235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14235)Memory used [KB]: 10618
% 0.21/0.53  % (14235)Time elapsed: 0.113 s
% 0.21/0.53  % (14235)------------------------------
% 0.21/0.53  % (14235)------------------------------
% 0.21/0.53  % (14248)Refutation not found, incomplete strategy% (14248)------------------------------
% 0.21/0.53  % (14248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14248)Memory used [KB]: 6268
% 0.21/0.53  % (14248)Time elapsed: 0.115 s
% 0.21/0.53  % (14248)------------------------------
% 0.21/0.53  % (14248)------------------------------
% 0.21/0.53  % (14249)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (14253)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (14258)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (14246)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.28/0.53  % (14251)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.28/0.53  % (14255)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.28/0.54  % (14257)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.28/0.54  % (14254)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.28/0.54  % (14241)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.28/0.54  % (14239)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.28/0.54  % (14244)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.28/0.55  % (14260)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.21/0.66  % (14244)Refutation not found, incomplete strategy% (14244)------------------------------
% 2.21/0.66  % (14244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (14244)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (14244)Memory used [KB]: 6140
% 2.21/0.66  % (14244)Time elapsed: 0.240 s
% 2.21/0.66  % (14244)------------------------------
% 2.21/0.66  % (14244)------------------------------
% 3.58/0.85  % (14260)Refutation found. Thanks to Tanya!
% 3.58/0.85  % SZS status Theorem for theBenchmark
% 3.58/0.85  % SZS output start Proof for theBenchmark
% 3.58/0.85  fof(f4076,plain,(
% 3.58/0.85    $false),
% 3.58/0.85    inference(avatar_sat_refutation,[],[f122,f131,f1761,f2503,f2847,f2850,f2920,f3831,f4057,f4063,f4073])).
% 3.58/0.85  fof(f4073,plain,(
% 3.58/0.85    ~spl11_4 | spl11_66 | ~spl11_87 | ~spl11_89 | ~spl11_104),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f4072])).
% 3.58/0.85  fof(f4072,plain,(
% 3.58/0.85    $false | (~spl11_4 | spl11_66 | ~spl11_87 | ~spl11_89 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f4055,f4067])).
% 3.58/0.85  fof(f4067,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | (spl11_66 | ~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f4066,f1760])).
% 3.58/0.85  fof(f1760,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | spl11_66),
% 3.58/0.85    inference(avatar_component_clause,[],[f1758])).
% 3.58/0.85  fof(f1758,plain,(
% 3.58/0.85    spl11_66 <=> r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).
% 3.58/0.85  fof(f4066,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f3663,f142])).
% 3.58/0.85  fof(f142,plain,(
% 3.58/0.85    l1_struct_0(sK8)),
% 3.58/0.85    inference(resolution,[],[f139,f76])).
% 3.58/0.85  fof(f76,plain,(
% 3.58/0.85    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f19])).
% 3.58/0.85  fof(f19,plain,(
% 3.58/0.85    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.58/0.85    inference(ennf_transformation,[],[f6])).
% 3.58/0.85  fof(f6,axiom,(
% 3.58/0.85    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.58/0.85  fof(f139,plain,(
% 3.58/0.85    l1_pre_topc(sK8)),
% 3.58/0.85    inference(subsumption_resolution,[],[f135,f63])).
% 3.58/0.85  fof(f63,plain,(
% 3.58/0.85    l1_pre_topc(sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f42,plain,(
% 3.58/0.85    ((((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.58/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f41,f40,f39,f38])).
% 3.58/0.85  fof(f38,plain,(
% 3.58/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.58/0.85    introduced(choice_axiom,[])).
% 3.58/0.85  fof(f39,plain,(
% 3.58/0.85    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6))),
% 3.58/0.85    introduced(choice_axiom,[])).
% 3.58/0.85  fof(f40,plain,(
% 3.58/0.85    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7))),
% 3.58/0.85    introduced(choice_axiom,[])).
% 3.58/0.85  fof(f41,plain,(
% 3.58/0.85    ? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8))),
% 3.58/0.85    introduced(choice_axiom,[])).
% 3.58/0.85  fof(f16,plain,(
% 3.58/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/0.85    inference(flattening,[],[f15])).
% 3.58/0.85  fof(f15,plain,(
% 3.58/0.85    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.58/0.85    inference(ennf_transformation,[],[f14])).
% 3.58/0.85  fof(f14,negated_conjecture,(
% 3.58/0.85    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.58/0.85    inference(negated_conjecture,[],[f13])).
% 3.58/0.85  fof(f13,conjecture,(
% 3.58/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 3.58/0.85  fof(f135,plain,(
% 3.58/0.85    l1_pre_topc(sK8) | ~l1_pre_topc(sK5)),
% 3.58/0.85    inference(resolution,[],[f92,f69])).
% 3.58/0.85  fof(f69,plain,(
% 3.58/0.85    m1_pre_topc(sK8,sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f92,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f21])).
% 3.58/0.85  fof(f21,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.58/0.85    inference(ennf_transformation,[],[f7])).
% 3.58/0.85  fof(f7,axiom,(
% 3.58/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 3.58/0.85  fof(f3663,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | ~l1_struct_0(sK8) | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(superposition,[],[f3633,f145])).
% 3.58/0.85  fof(f145,plain,(
% 3.58/0.85    k2_struct_0(sK8) = u1_struct_0(sK8)),
% 3.58/0.85    inference(resolution,[],[f142,f73])).
% 3.58/0.85  fof(f73,plain,(
% 3.58/0.85    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f17])).
% 3.58/0.85  fof(f17,plain,(
% 3.58/0.85    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.58/0.85    inference(ennf_transformation,[],[f4])).
% 3.58/0.85  fof(f4,axiom,(
% 3.58/0.85    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.58/0.85  fof(f3633,plain,(
% 3.58/0.85    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) | ~l1_struct_0(X0) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f3624])).
% 3.58/0.85  fof(f3624,plain,(
% 3.58/0.85    ( ! [X0] : (~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) | ~l1_struct_0(X0)) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(resolution,[],[f3547,f3078])).
% 3.58/0.85  fof(f3078,plain,(
% 3.58/0.85    ( ! [X1] : (~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | ~l1_struct_0(X1)) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f2971,f2527])).
% 3.58/0.85  fof(f2527,plain,(
% 3.58/0.85    l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~spl11_104),
% 3.58/0.85    inference(resolution,[],[f2526,f76])).
% 3.58/0.85  fof(f2526,plain,(
% 3.58/0.85    l1_pre_topc(k1_tsep_1(sK7,sK6,sK6)) | ~spl11_104),
% 3.58/0.85    inference(subsumption_resolution,[],[f2511,f138])).
% 3.58/0.85  fof(f138,plain,(
% 3.58/0.85    l1_pre_topc(sK7)),
% 3.58/0.85    inference(subsumption_resolution,[],[f134,f63])).
% 3.58/0.85  fof(f134,plain,(
% 3.58/0.85    l1_pre_topc(sK7) | ~l1_pre_topc(sK5)),
% 3.58/0.85    inference(resolution,[],[f92,f67])).
% 3.58/0.85  fof(f67,plain,(
% 3.58/0.85    m1_pre_topc(sK7,sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f2511,plain,(
% 3.58/0.85    l1_pre_topc(k1_tsep_1(sK7,sK6,sK6)) | ~l1_pre_topc(sK7) | ~spl11_104),
% 3.58/0.85    inference(resolution,[],[f2493,f92])).
% 3.58/0.85  fof(f2493,plain,(
% 3.58/0.85    m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) | ~spl11_104),
% 3.58/0.85    inference(avatar_component_clause,[],[f2492])).
% 3.58/0.85  fof(f2492,plain,(
% 3.58/0.85    spl11_104 <=> m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).
% 3.58/0.85  fof(f2971,plain,(
% 3.58/0.85    ( ! [X1] : (r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | ~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) ) | ~spl11_87),
% 3.58/0.85    inference(backward_demodulation,[],[f2400,f2200])).
% 3.58/0.85  fof(f2200,plain,(
% 3.58/0.85    k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) | ~spl11_87),
% 3.58/0.85    inference(avatar_component_clause,[],[f2198])).
% 3.58/0.85  fof(f2198,plain,(
% 3.58/0.85    spl11_87 <=> k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).
% 3.58/0.85  fof(f2400,plain,(
% 3.58/0.85    ( ! [X1] : (r1_xboole_0(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),u1_struct_0(X1)) | ~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) )),
% 3.58/0.85    inference(superposition,[],[f74,f2392])).
% 3.58/0.85  fof(f2392,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2391,f2162])).
% 3.58/0.85  fof(f2162,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2161,f921])).
% 3.58/0.85  fof(f921,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f917,f64])).
% 3.58/0.85  fof(f64,plain,(
% 3.58/0.85    ~v2_struct_0(sK6)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f917,plain,(
% 3.58/0.85    v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 3.58/0.85    inference(resolution,[],[f901,f65])).
% 3.58/0.85  fof(f65,plain,(
% 3.58/0.85    m1_pre_topc(sK6,sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f901,plain,(
% 3.58/0.85    ( ! [X8] : (~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f900,f61])).
% 3.58/0.85  fof(f61,plain,(
% 3.58/0.85    ~v2_struct_0(sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f900,plain,(
% 3.58/0.85    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f899,f63])).
% 3.58/0.85  fof(f899,plain,(
% 3.58/0.85    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f885,f64])).
% 3.58/0.85  fof(f885,plain,(
% 3.58/0.85    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 3.58/0.85    inference(resolution,[],[f675,f65])).
% 3.58/0.85  fof(f675,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f674])).
% 3.58/0.85  fof(f674,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 3.58/0.85    inference(resolution,[],[f108,f449])).
% 3.58/0.85  fof(f449,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~l1_pre_topc(X0) | k2_struct_0(k1_tsep_1(X0,X2,X1)) = u1_struct_0(k1_tsep_1(X0,X2,X1))) )),
% 3.58/0.85    inference(resolution,[],[f448,f73])).
% 3.58/0.85  fof(f448,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (l1_struct_0(k1_tsep_1(X0,X2,X1)) | ~l1_pre_topc(X0) | ~sP4(X0,X1,X2)) )),
% 3.58/0.85    inference(resolution,[],[f165,f76])).
% 3.58/0.85  fof(f165,plain,(
% 3.58/0.85    ( ! [X4,X5,X3] : (l1_pre_topc(k1_tsep_1(X3,X5,X4)) | ~sP4(X3,X4,X5) | ~l1_pre_topc(X3)) )),
% 3.58/0.85    inference(resolution,[],[f107,f92])).
% 3.58/0.85  fof(f107,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f60])).
% 3.58/0.85  fof(f60,plain,(
% 3.58/0.85    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP4(X0,X1,X2))),
% 3.58/0.85    inference(rectify,[],[f59])).
% 3.58/0.85  fof(f59,plain,(
% 3.58/0.85    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 3.58/0.85    inference(nnf_transformation,[],[f36])).
% 3.58/0.85  fof(f36,plain,(
% 3.58/0.85    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 3.58/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.58/0.85  fof(f108,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f37])).
% 3.58/0.85  fof(f37,plain,(
% 3.58/0.85    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.85    inference(definition_folding,[],[f30,f36])).
% 3.58/0.85  fof(f30,plain,(
% 3.58/0.85    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.85    inference(flattening,[],[f29])).
% 3.58/0.85  fof(f29,plain,(
% 3.58/0.85    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.85    inference(ennf_transformation,[],[f10])).
% 3.58/0.85  fof(f10,axiom,(
% 3.58/0.85    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 3.58/0.85  fof(f2161,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2160,f143])).
% 3.58/0.85  fof(f143,plain,(
% 3.58/0.85    k2_struct_0(sK6) = u1_struct_0(sK6)),
% 3.58/0.85    inference(resolution,[],[f140,f73])).
% 3.58/0.85  fof(f140,plain,(
% 3.58/0.85    l1_struct_0(sK6)),
% 3.58/0.85    inference(resolution,[],[f137,f76])).
% 3.58/0.85  fof(f137,plain,(
% 3.58/0.85    l1_pre_topc(sK6)),
% 3.58/0.85    inference(subsumption_resolution,[],[f133,f63])).
% 3.58/0.85  fof(f133,plain,(
% 3.58/0.85    l1_pre_topc(sK6) | ~l1_pre_topc(sK5)),
% 3.58/0.85    inference(resolution,[],[f92,f65])).
% 3.58/0.85  fof(f2160,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2156,f64])).
% 3.58/0.85  fof(f2156,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) | v2_struct_0(sK6)),
% 3.58/0.85    inference(resolution,[],[f2075,f65])).
% 3.58/0.85  fof(f2075,plain,(
% 3.58/0.85    ( ! [X8] : (~m1_pre_topc(X8,sK5) | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6)) | v2_struct_0(X8)) )),
% 3.58/0.85    inference(forward_demodulation,[],[f2074,f143])).
% 3.58/0.85  fof(f2074,plain,(
% 3.58/0.85    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2073,f61])).
% 3.58/0.85  fof(f2073,plain,(
% 3.58/0.85    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | v2_struct_0(sK5)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2072,f63])).
% 3.58/0.85  fof(f2072,plain,(
% 3.58/0.85    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2057,f64])).
% 3.58/0.85  fof(f2057,plain,(
% 3.58/0.85    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 3.58/0.85    inference(resolution,[],[f1526,f65])).
% 3.58/0.85  fof(f1526,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f1525,f108])).
% 3.58/0.85  fof(f1525,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f1524,f105])).
% 3.58/0.85  fof(f105,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f60])).
% 3.58/0.85  fof(f1524,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f1523,f106])).
% 3.58/0.85  fof(f106,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f60])).
% 3.58/0.85  fof(f1523,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~v1_pre_topc(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 3.58/0.85    inference(resolution,[],[f110,f107])).
% 3.58/0.85  fof(f110,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.85    inference(equality_resolution,[],[f93])).
% 3.58/0.85  fof(f93,plain,(
% 3.58/0.85    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f55])).
% 3.58/0.85  fof(f55,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.85    inference(nnf_transformation,[],[f23])).
% 3.58/0.85  fof(f23,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.85    inference(flattening,[],[f22])).
% 3.58/0.85  fof(f22,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.85    inference(ennf_transformation,[],[f8])).
% 3.58/0.85  fof(f8,axiom,(
% 3.58/0.85    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 3.58/0.85  fof(f2391,plain,(
% 3.58/0.85    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2390,f143])).
% 3.58/0.85  fof(f2390,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2387,f64])).
% 3.58/0.85  fof(f2387,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | v2_struct_0(sK6)),
% 3.58/0.85    inference(resolution,[],[f2090,f70])).
% 3.58/0.85  fof(f70,plain,(
% 3.58/0.85    m1_pre_topc(sK6,sK7)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f2090,plain,(
% 3.58/0.85    ( ! [X12] : (~m1_pre_topc(X12,sK7) | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6)) | v2_struct_0(X12)) )),
% 3.58/0.85    inference(forward_demodulation,[],[f2089,f143])).
% 3.58/0.85  fof(f2089,plain,(
% 3.58/0.85    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2088,f66])).
% 3.58/0.85  fof(f66,plain,(
% 3.58/0.85    ~v2_struct_0(sK7)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f2088,plain,(
% 3.58/0.85    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | v2_struct_0(sK7)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2087,f138])).
% 3.58/0.85  fof(f2087,plain,(
% 3.58/0.85    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2061,f64])).
% 3.58/0.85  fof(f2061,plain,(
% 3.58/0.85    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 3.58/0.85    inference(resolution,[],[f1526,f70])).
% 3.58/0.85  fof(f74,plain,(
% 3.58/0.85    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f43])).
% 3.58/0.85  fof(f43,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.58/0.85    inference(nnf_transformation,[],[f18])).
% 3.58/0.85  fof(f18,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.58/0.85    inference(ennf_transformation,[],[f9])).
% 3.58/0.85  fof(f9,axiom,(
% 3.58/0.85    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 3.58/0.85  fof(f3547,plain,(
% 3.58/0.85    ( ! [X1] : (r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f3545,f2527])).
% 3.58/0.85  fof(f3545,plain,(
% 3.58/0.85    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | ~l1_struct_0(X1) | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f3538])).
% 3.58/0.85  fof(f3538,plain,(
% 3.58/0.85    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | ~l1_struct_0(X1) | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X1)) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(resolution,[],[f3081,f98])).
% 3.58/0.85  fof(f98,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f27])).
% 3.58/0.85  fof(f27,plain,(
% 3.58/0.85    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.58/0.85    inference(flattening,[],[f26])).
% 3.58/0.85  fof(f26,plain,(
% 3.58/0.85    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.58/0.85    inference(ennf_transformation,[],[f11])).
% 3.58/0.85  fof(f11,axiom,(
% 3.58/0.85    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 3.58/0.85  fof(f3081,plain,(
% 3.58/0.85    ( ! [X4] : (r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6)) | ~l1_struct_0(X4)) ) | (~spl11_87 | ~spl11_104)),
% 3.58/0.85    inference(subsumption_resolution,[],[f2974,f2527])).
% 3.58/0.85  fof(f2974,plain,(
% 3.58/0.85    ( ! [X4] : (~r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6)) | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X4)) ) | ~spl11_87),
% 3.58/0.85    inference(backward_demodulation,[],[f2403,f2200])).
% 3.58/0.85  fof(f2403,plain,(
% 3.58/0.85    ( ! [X4] : (~r1_xboole_0(u1_struct_0(X4),k2_struct_0(k1_tsep_1(sK5,sK6,sK6))) | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X4)) )),
% 3.58/0.85    inference(superposition,[],[f75,f2392])).
% 3.58/0.85  fof(f75,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f43])).
% 3.58/0.85  fof(f4055,plain,(
% 3.58/0.85    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | (~spl11_4 | ~spl11_89)),
% 3.58/0.85    inference(resolution,[],[f3879,f1513])).
% 3.58/0.85  fof(f1513,plain,(
% 3.58/0.85    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~spl11_4),
% 3.58/0.85    inference(subsumption_resolution,[],[f1359,f130])).
% 3.58/0.85  fof(f130,plain,(
% 3.58/0.85    r1_tsep_1(sK8,sK7) | ~spl11_4),
% 3.58/0.85    inference(avatar_component_clause,[],[f128])).
% 3.58/0.85  fof(f128,plain,(
% 3.58/0.85    spl11_4 <=> r1_tsep_1(sK8,sK7)),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 3.58/0.85  fof(f1359,plain,(
% 3.58/0.85    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~r1_tsep_1(sK8,sK7)),
% 3.58/0.85    inference(subsumption_resolution,[],[f389,f142])).
% 3.58/0.85  fof(f389,plain,(
% 3.58/0.85    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK8)),
% 3.58/0.85    inference(superposition,[],[f186,f145])).
% 3.58/0.85  fof(f186,plain,(
% 3.58/0.85    ( ! [X2] : (r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK7)) | ~r1_tsep_1(X2,sK7) | ~l1_struct_0(X2)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f178,f141])).
% 3.58/0.85  fof(f141,plain,(
% 3.58/0.85    l1_struct_0(sK7)),
% 3.58/0.85    inference(resolution,[],[f138,f76])).
% 3.58/0.85  fof(f178,plain,(
% 3.58/0.85    ( ! [X2] : (r1_xboole_0(u1_struct_0(X2),k2_struct_0(sK7)) | ~r1_tsep_1(X2,sK7) | ~l1_struct_0(sK7) | ~l1_struct_0(X2)) )),
% 3.58/0.85    inference(superposition,[],[f74,f144])).
% 3.58/0.85  fof(f144,plain,(
% 3.58/0.85    k2_struct_0(sK7) = u1_struct_0(sK7)),
% 3.58/0.85    inference(resolution,[],[f141,f73])).
% 3.58/0.85  fof(f3879,plain,(
% 3.58/0.85    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(sK7)) | r1_xboole_0(X1,k2_struct_0(sK6))) ) | ~spl11_89),
% 3.58/0.85    inference(backward_demodulation,[],[f2180,f2222])).
% 3.58/0.85  fof(f2222,plain,(
% 3.58/0.85    k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~spl11_89),
% 3.58/0.85    inference(avatar_component_clause,[],[f2220])).
% 3.58/0.85  fof(f2220,plain,(
% 3.58/0.85    spl11_89 <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).
% 3.58/0.85  fof(f2180,plain,(
% 3.58/0.85    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK5,sK7,sK6))) | r1_xboole_0(X1,k2_struct_0(sK6))) )),
% 3.58/0.85    inference(superposition,[],[f104,f2165])).
% 3.58/0.85  fof(f2165,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2164,f1106])).
% 3.58/0.85  fof(f1106,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f1102,f64])).
% 3.58/0.85  fof(f1102,plain,(
% 3.58/0.85    v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 3.58/0.85    inference(resolution,[],[f904,f65])).
% 3.58/0.85  fof(f904,plain,(
% 3.58/0.85    ( ! [X9] : (~m1_pre_topc(X9,sK5) | v2_struct_0(X9) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f903,f61])).
% 3.58/0.85  fof(f903,plain,(
% 3.58/0.85    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f902,f63])).
% 3.58/0.85  fof(f902,plain,(
% 3.58/0.85    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f886,f66])).
% 3.58/0.85  fof(f886,plain,(
% 3.58/0.85    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 3.58/0.85    inference(resolution,[],[f675,f67])).
% 3.58/0.85  fof(f2164,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2163,f144])).
% 3.58/0.85  fof(f2163,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2157,f66])).
% 3.58/0.85  fof(f2157,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) | v2_struct_0(sK7)),
% 3.58/0.85    inference(resolution,[],[f2075,f67])).
% 3.58/0.85  fof(f104,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f28])).
% 3.58/0.85  fof(f28,plain,(
% 3.58/0.85    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.58/0.85    inference(ennf_transformation,[],[f2])).
% 3.58/0.85  fof(f2,axiom,(
% 3.58/0.85    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.58/0.85  fof(f4063,plain,(
% 3.58/0.85    ~spl11_3 | spl11_4),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f4062])).
% 3.58/0.85  fof(f4062,plain,(
% 3.58/0.85    $false | (~spl11_3 | spl11_4)),
% 3.58/0.85    inference(subsumption_resolution,[],[f162,f129])).
% 3.58/0.85  fof(f129,plain,(
% 3.58/0.85    ~r1_tsep_1(sK8,sK7) | spl11_4),
% 3.58/0.85    inference(avatar_component_clause,[],[f128])).
% 3.58/0.85  fof(f162,plain,(
% 3.58/0.85    r1_tsep_1(sK8,sK7) | ~spl11_3),
% 3.58/0.85    inference(subsumption_resolution,[],[f161,f141])).
% 3.58/0.85  fof(f161,plain,(
% 3.58/0.85    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK7) | ~spl11_3),
% 3.58/0.85    inference(subsumption_resolution,[],[f160,f142])).
% 3.58/0.85  fof(f160,plain,(
% 3.58/0.85    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK8) | ~l1_struct_0(sK7) | ~spl11_3),
% 3.58/0.85    inference(resolution,[],[f98,f126])).
% 3.58/0.85  fof(f126,plain,(
% 3.58/0.85    r1_tsep_1(sK7,sK8) | ~spl11_3),
% 3.58/0.85    inference(avatar_component_clause,[],[f124])).
% 3.58/0.85  fof(f124,plain,(
% 3.58/0.85    spl11_3 <=> r1_tsep_1(sK7,sK8)),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 3.58/0.85  fof(f4057,plain,(
% 3.58/0.85    spl11_2 | ~spl11_4 | ~spl11_89),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f4056])).
% 3.58/0.85  fof(f4056,plain,(
% 3.58/0.85    $false | (spl11_2 | ~spl11_4 | ~spl11_89)),
% 3.58/0.85    inference(subsumption_resolution,[],[f4055,f427])).
% 3.58/0.85  fof(f427,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | spl11_2),
% 3.58/0.85    inference(subsumption_resolution,[],[f426,f140])).
% 3.58/0.85  fof(f426,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | ~l1_struct_0(sK6) | spl11_2),
% 3.58/0.85    inference(subsumption_resolution,[],[f422,f121])).
% 3.58/0.85  fof(f121,plain,(
% 3.58/0.85    ~r1_tsep_1(sK8,sK6) | spl11_2),
% 3.58/0.85    inference(avatar_component_clause,[],[f119])).
% 3.58/0.85  fof(f119,plain,(
% 3.58/0.85    spl11_2 <=> r1_tsep_1(sK8,sK6)),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 3.58/0.85  fof(f422,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_tsep_1(sK8,sK6) | ~l1_struct_0(sK6)),
% 3.58/0.85    inference(superposition,[],[f320,f143])).
% 3.58/0.85  fof(f320,plain,(
% 3.58/0.85    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | r1_tsep_1(sK8,X3) | ~l1_struct_0(X3)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f311,f142])).
% 3.58/0.85  fof(f311,plain,(
% 3.58/0.85    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | r1_tsep_1(sK8,X3) | ~l1_struct_0(X3) | ~l1_struct_0(sK8)) )),
% 3.58/0.85    inference(superposition,[],[f75,f145])).
% 3.58/0.85  fof(f3831,plain,(
% 3.58/0.85    spl11_75),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f3830])).
% 3.58/0.85  fof(f3830,plain,(
% 3.58/0.85    $false | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3829,f138])).
% 3.58/0.85  fof(f3829,plain,(
% 3.58/0.85    ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3828,f66])).
% 3.58/0.85  fof(f3828,plain,(
% 3.58/0.85    v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3827,f545])).
% 3.58/0.85  fof(f545,plain,(
% 3.58/0.85    m1_pre_topc(sK7,sK7)),
% 3.58/0.85    inference(subsumption_resolution,[],[f544,f62])).
% 3.58/0.85  fof(f62,plain,(
% 3.58/0.85    v2_pre_topc(sK5)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f544,plain,(
% 3.58/0.85    m1_pre_topc(sK7,sK7) | ~v2_pre_topc(sK5)),
% 3.58/0.85    inference(subsumption_resolution,[],[f538,f63])).
% 3.58/0.85  fof(f538,plain,(
% 3.58/0.85    m1_pre_topc(sK7,sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 3.58/0.85    inference(resolution,[],[f536,f67])).
% 3.58/0.85  fof(f536,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f527])).
% 3.58/0.85  fof(f527,plain,(
% 3.58/0.85    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 3.58/0.85    inference(resolution,[],[f95,f111])).
% 3.58/0.85  fof(f111,plain,(
% 3.58/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.58/0.85    inference(equality_resolution,[],[f100])).
% 3.58/0.85  fof(f100,plain,(
% 3.58/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.58/0.85    inference(cnf_transformation,[],[f58])).
% 3.58/0.85  fof(f58,plain,(
% 3.58/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.58/0.85    inference(flattening,[],[f57])).
% 3.58/0.85  fof(f57,plain,(
% 3.58/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.58/0.85    inference(nnf_transformation,[],[f1])).
% 3.58/0.85  fof(f1,axiom,(
% 3.58/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.58/0.85  fof(f95,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f56])).
% 3.58/0.85  fof(f56,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.85    inference(nnf_transformation,[],[f25])).
% 3.58/0.85  fof(f25,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.85    inference(flattening,[],[f24])).
% 3.58/0.85  fof(f24,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.58/0.85    inference(ennf_transformation,[],[f12])).
% 3.58/0.85  fof(f12,axiom,(
% 3.58/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 3.58/0.85  fof(f3827,plain,(
% 3.58/0.85    ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3826,f64])).
% 3.58/0.85  fof(f3826,plain,(
% 3.58/0.85    v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3825,f70])).
% 3.58/0.85  fof(f3825,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f3824])).
% 3.58/0.85  fof(f3824,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_75),
% 3.58/0.85    inference(resolution,[],[f3823,f108])).
% 3.58/0.85  fof(f3823,plain,(
% 3.58/0.85    ~sP4(sK7,sK6,sK7) | spl11_75),
% 3.58/0.85    inference(subsumption_resolution,[],[f3822,f138])).
% 3.58/0.85  fof(f3822,plain,(
% 3.58/0.85    ~sP4(sK7,sK6,sK7) | ~l1_pre_topc(sK7) | spl11_75),
% 3.58/0.85    inference(resolution,[],[f3807,f164])).
% 3.58/0.85  fof(f164,plain,(
% 3.58/0.85    ( ! [X2,X0,X1] : (sP2(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2) | ~l1_pre_topc(X0)) )),
% 3.58/0.85    inference(resolution,[],[f107,f147])).
% 3.58/0.85  fof(f147,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X1)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f146,f92])).
% 3.58/0.85  fof(f146,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 3.58/0.85    inference(resolution,[],[f77,f91])).
% 3.58/0.85  fof(f91,plain,(
% 3.58/0.85    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f35])).
% 3.58/0.85  fof(f35,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : (sP3(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.58/0.85    inference(definition_folding,[],[f20,f34,f33,f32,f31])).
% 3.58/0.85  fof(f31,plain,(
% 3.58/0.85    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.58/0.85  fof(f32,plain,(
% 3.58/0.85    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> sP0(X2,X1,X0)))),
% 3.58/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.58/0.85  fof(f33,plain,(
% 3.58/0.85    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 3.58/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.58/0.85  fof(f34,plain,(
% 3.58/0.85    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 3.58/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.58/0.85  fof(f20,plain,(
% 3.58/0.85    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.58/0.85    inference(ennf_transformation,[],[f5])).
% 3.58/0.85  fof(f5,axiom,(
% 3.58/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 3.58/0.85  fof(f77,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~sP3(X0,X1) | ~m1_pre_topc(X1,X0) | sP2(X1,X0)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f44])).
% 3.58/0.85  fof(f44,plain,(
% 3.58/0.85    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP3(X0,X1))),
% 3.58/0.85    inference(nnf_transformation,[],[f34])).
% 3.58/0.85  fof(f3807,plain,(
% 3.58/0.85    ~sP2(k1_tsep_1(sK7,sK7,sK6),sK7) | spl11_75),
% 3.58/0.85    inference(resolution,[],[f3785,f2034])).
% 3.58/0.85  fof(f2034,plain,(
% 3.58/0.85    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | spl11_75),
% 3.58/0.85    inference(avatar_component_clause,[],[f2033])).
% 3.58/0.85  fof(f2033,plain,(
% 3.58/0.85    spl11_75 <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_75])])).
% 3.58/0.85  fof(f3785,plain,(
% 3.58/0.85    ( ! [X0] : (r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0)) | ~sP2(k1_tsep_1(sK7,sK7,sK6),X0)) )),
% 3.58/0.85    inference(superposition,[],[f79,f3773])).
% 3.58/0.85  fof(f3773,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f3772,f2395])).
% 3.58/0.85  fof(f2395,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2394,f2165])).
% 3.58/0.85  fof(f2394,plain,(
% 3.58/0.85    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2393,f144])).
% 3.58/0.85  fof(f2393,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2388,f66])).
% 3.58/0.85  fof(f2388,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(sK7)),
% 3.58/0.85    inference(resolution,[],[f2090,f545])).
% 3.58/0.85  fof(f3772,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f3767,f64])).
% 3.58/0.85  fof(f3767,plain,(
% 3.58/0.85    v2_struct_0(sK6) | u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 3.58/0.85    inference(resolution,[],[f914,f70])).
% 3.58/0.85  fof(f914,plain,(
% 3.58/0.85    ( ! [X13] : (~m1_pre_topc(X13,sK7) | v2_struct_0(X13) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f913,f138])).
% 3.58/0.85  fof(f913,plain,(
% 3.58/0.85    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | ~l1_pre_topc(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f893,f66])).
% 3.58/0.85  fof(f893,plain,(
% 3.58/0.85    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f890])).
% 3.58/0.85  fof(f890,plain,(
% 3.58/0.85    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 3.58/0.85    inference(resolution,[],[f675,f545])).
% 3.58/0.85  fof(f79,plain,(
% 3.58/0.85    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP2(X0,X1)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f49])).
% 3.58/0.85  fof(f49,plain,(
% 3.58/0.85    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 3.58/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 3.58/0.85  fof(f48,plain,(
% 3.58/0.85    ! [X1,X0] : (? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.85    introduced(choice_axiom,[])).
% 3.58/0.85  fof(f47,plain,(
% 3.58/0.85    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 3.58/0.85    inference(rectify,[],[f46])).
% 3.58/0.85  fof(f46,plain,(
% 3.58/0.85    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 3.58/0.85    inference(flattening,[],[f45])).
% 3.58/0.85  fof(f45,plain,(
% 3.58/0.85    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 3.58/0.85    inference(nnf_transformation,[],[f33])).
% 3.58/0.85  fof(f2920,plain,(
% 3.58/0.85    spl11_108),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f2919])).
% 3.58/0.85  fof(f2919,plain,(
% 3.58/0.85    $false | spl11_108),
% 3.58/0.85    inference(subsumption_resolution,[],[f2918,f137])).
% 3.58/0.85  fof(f2918,plain,(
% 3.58/0.85    ~l1_pre_topc(sK6) | spl11_108),
% 3.58/0.85    inference(subsumption_resolution,[],[f2917,f64])).
% 3.58/0.85  fof(f2917,plain,(
% 3.58/0.85    v2_struct_0(sK6) | ~l1_pre_topc(sK6) | spl11_108),
% 3.58/0.85    inference(subsumption_resolution,[],[f2916,f543])).
% 3.58/0.85  fof(f543,plain,(
% 3.58/0.85    m1_pre_topc(sK6,sK6)),
% 3.58/0.85    inference(subsumption_resolution,[],[f542,f62])).
% 3.58/0.85  fof(f542,plain,(
% 3.58/0.85    m1_pre_topc(sK6,sK6) | ~v2_pre_topc(sK5)),
% 3.58/0.85    inference(subsumption_resolution,[],[f537,f63])).
% 3.58/0.85  fof(f537,plain,(
% 3.58/0.85    m1_pre_topc(sK6,sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 3.58/0.85    inference(resolution,[],[f536,f65])).
% 3.58/0.85  fof(f2916,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | spl11_108),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f2915])).
% 3.58/0.85  fof(f2915,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | v2_struct_0(sK6) | spl11_108),
% 3.58/0.85    inference(resolution,[],[f2914,f108])).
% 3.58/0.85  fof(f2914,plain,(
% 3.58/0.85    ~sP4(sK6,sK6,sK6) | spl11_108),
% 3.58/0.85    inference(subsumption_resolution,[],[f2913,f137])).
% 3.58/0.85  fof(f2913,plain,(
% 3.58/0.85    ~sP4(sK6,sK6,sK6) | ~l1_pre_topc(sK6) | spl11_108),
% 3.58/0.85    inference(resolution,[],[f2906,f164])).
% 3.58/0.85  fof(f2906,plain,(
% 3.58/0.85    ~sP2(k1_tsep_1(sK6,sK6,sK6),sK6) | spl11_108),
% 3.58/0.85    inference(resolution,[],[f2895,f2846])).
% 3.58/0.85  fof(f2846,plain,(
% 3.58/0.85    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) | spl11_108),
% 3.58/0.85    inference(avatar_component_clause,[],[f2844])).
% 3.58/0.85  fof(f2844,plain,(
% 3.58/0.85    spl11_108 <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_108])])).
% 3.58/0.85  fof(f2895,plain,(
% 3.58/0.85    ( ! [X0] : (r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(X0)) | ~sP2(k1_tsep_1(sK6,sK6,sK6),X0)) )),
% 3.58/0.85    inference(superposition,[],[f79,f2889])).
% 3.58/0.85  fof(f2889,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2888,f2589])).
% 3.58/0.85  fof(f2589,plain,(
% 3.58/0.85    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2588,f2162])).
% 3.58/0.85  fof(f2588,plain,(
% 3.58/0.85    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(forward_demodulation,[],[f2587,f143])).
% 3.58/0.85  fof(f2587,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2585,f64])).
% 3.58/0.85  fof(f2585,plain,(
% 3.58/0.85    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) | v2_struct_0(sK6)),
% 3.58/0.85    inference(resolution,[],[f2086,f543])).
% 3.58/0.85  fof(f2086,plain,(
% 3.58/0.85    ( ! [X11] : (~m1_pre_topc(X11,sK6) | u1_struct_0(k1_tsep_1(sK6,X11,sK6)) = k2_xboole_0(u1_struct_0(X11),k2_struct_0(sK6)) | v2_struct_0(X11)) )),
% 3.58/0.85    inference(forward_demodulation,[],[f2085,f143])).
% 3.58/0.85  fof(f2085,plain,(
% 3.58/0.85    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2084,f137])).
% 3.58/0.85  fof(f2084,plain,(
% 3.58/0.85    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f2067,f64])).
% 3.58/0.85  fof(f2067,plain,(
% 3.58/0.85    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6)) )),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f2060])).
% 3.58/0.85  fof(f2060,plain,(
% 3.58/0.85    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 3.58/0.85    inference(resolution,[],[f1526,f543])).
% 3.58/0.85  fof(f2888,plain,(
% 3.58/0.85    u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(subsumption_resolution,[],[f2886,f64])).
% 3.58/0.85  fof(f2886,plain,(
% 3.58/0.85    v2_struct_0(sK6) | u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 3.58/0.85    inference(resolution,[],[f909,f543])).
% 3.58/0.85  fof(f909,plain,(
% 3.58/0.85    ( ! [X11] : (~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f908,f137])).
% 3.58/0.85  fof(f908,plain,(
% 3.58/0.85    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | ~l1_pre_topc(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f894,f64])).
% 3.58/0.85  fof(f894,plain,(
% 3.58/0.85    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f888])).
% 3.58/0.85  fof(f888,plain,(
% 3.58/0.85    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 3.58/0.85    inference(resolution,[],[f675,f543])).
% 3.58/0.85  fof(f2850,plain,(
% 3.58/0.85    spl11_89 | ~spl11_75),
% 3.58/0.85    inference(avatar_split_clause,[],[f2179,f2033,f2220])).
% 3.58/0.85  fof(f2179,plain,(
% 3.58/0.85    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 3.58/0.85    inference(superposition,[],[f158,f2165])).
% 3.58/0.85  fof(f158,plain,(
% 3.58/0.85    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 3.58/0.85    inference(resolution,[],[f101,f97])).
% 3.58/0.85  fof(f97,plain,(
% 3.58/0.85    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.58/0.85    inference(cnf_transformation,[],[f3])).
% 3.58/0.85  fof(f3,axiom,(
% 3.58/0.85    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.58/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.58/0.85  fof(f101,plain,(
% 3.58/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.58/0.85    inference(cnf_transformation,[],[f58])).
% 3.58/0.85  fof(f2847,plain,(
% 3.58/0.85    spl11_87 | ~spl11_108),
% 3.58/0.85    inference(avatar_split_clause,[],[f2171,f2844,f2198])).
% 3.58/0.85  fof(f2171,plain,(
% 3.58/0.85    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) | k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 3.58/0.85    inference(superposition,[],[f158,f2162])).
% 3.58/0.85  fof(f2503,plain,(
% 3.58/0.85    spl11_104),
% 3.58/0.85    inference(avatar_contradiction_clause,[],[f2502])).
% 3.58/0.85  fof(f2502,plain,(
% 3.58/0.85    $false | spl11_104),
% 3.58/0.85    inference(subsumption_resolution,[],[f2501,f66])).
% 3.58/0.85  fof(f2501,plain,(
% 3.58/0.85    v2_struct_0(sK7) | spl11_104),
% 3.58/0.85    inference(subsumption_resolution,[],[f2500,f138])).
% 3.58/0.85  fof(f2500,plain,(
% 3.58/0.85    ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_104),
% 3.58/0.85    inference(subsumption_resolution,[],[f2499,f64])).
% 3.58/0.85  fof(f2499,plain,(
% 3.58/0.85    v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_104),
% 3.58/0.85    inference(subsumption_resolution,[],[f2498,f70])).
% 3.58/0.85  fof(f2498,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_104),
% 3.58/0.85    inference(duplicate_literal_removal,[],[f2497])).
% 3.58/0.85  fof(f2497,plain,(
% 3.58/0.85    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_104),
% 3.58/0.85    inference(resolution,[],[f2496,f108])).
% 3.58/0.85  fof(f2496,plain,(
% 3.58/0.85    ~sP4(sK7,sK6,sK6) | spl11_104),
% 3.58/0.85    inference(resolution,[],[f2494,f107])).
% 3.58/0.85  fof(f2494,plain,(
% 3.58/0.85    ~m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) | spl11_104),
% 3.58/0.85    inference(avatar_component_clause,[],[f2492])).
% 3.58/0.85  fof(f1761,plain,(
% 3.58/0.85    spl11_1 | ~spl11_66),
% 3.58/0.85    inference(avatar_split_clause,[],[f1354,f1758,f115])).
% 3.58/0.85  fof(f115,plain,(
% 3.58/0.85    spl11_1 <=> r1_tsep_1(sK6,sK8)),
% 3.58/0.85    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 3.58/0.85  fof(f1354,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | r1_tsep_1(sK6,sK8)),
% 3.58/0.85    inference(subsumption_resolution,[],[f444,f140])).
% 3.58/0.85  fof(f444,plain,(
% 3.58/0.85    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK6)),
% 3.58/0.85    inference(superposition,[],[f324,f143])).
% 3.58/0.85  fof(f324,plain,(
% 3.58/0.85    ( ! [X3] : (~r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK8)) | r1_tsep_1(X3,sK8) | ~l1_struct_0(X3)) )),
% 3.58/0.85    inference(subsumption_resolution,[],[f315,f142])).
% 3.58/0.85  fof(f315,plain,(
% 3.58/0.85    ( ! [X3] : (~r1_xboole_0(u1_struct_0(X3),k2_struct_0(sK8)) | r1_tsep_1(X3,sK8) | ~l1_struct_0(sK8) | ~l1_struct_0(X3)) )),
% 3.58/0.85    inference(superposition,[],[f75,f145])).
% 3.58/0.85  fof(f131,plain,(
% 3.58/0.85    spl11_3 | spl11_4),
% 3.58/0.85    inference(avatar_split_clause,[],[f72,f128,f124])).
% 3.58/0.85  fof(f72,plain,(
% 3.58/0.85    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  fof(f122,plain,(
% 3.58/0.85    ~spl11_1 | ~spl11_2),
% 3.58/0.85    inference(avatar_split_clause,[],[f71,f119,f115])).
% 3.58/0.85  fof(f71,plain,(
% 3.58/0.85    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 3.58/0.85    inference(cnf_transformation,[],[f42])).
% 3.58/0.85  % SZS output end Proof for theBenchmark
% 3.58/0.85  % (14260)------------------------------
% 3.58/0.85  % (14260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.58/0.85  % (14260)Termination reason: Refutation
% 3.58/0.85  
% 3.58/0.85  % (14260)Memory used [KB]: 14328
% 3.58/0.85  % (14260)Time elapsed: 0.410 s
% 3.58/0.85  % (14260)------------------------------
% 3.58/0.85  % (14260)------------------------------
% 3.58/0.85  % (14234)Success in time 0.49 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 4.07s
% Output     : Refutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  282 (4407 expanded)
%              Number of leaves         :   32 (1684 expanded)
%              Depth                    :   33
%              Number of atoms          : 1093 (47316 expanded)
%              Number of equality atoms :  104 ( 646 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f131,f2481,f2821,f2826,f2894,f3871,f4097,f4106,f4122])).

fof(f4122,plain,
    ( ~ spl11_2
    | spl11_3
    | ~ spl11_86
    | ~ spl11_88
    | ~ spl11_103 ),
    inference(avatar_contradiction_clause,[],[f4121])).

fof(f4121,plain,
    ( $false
    | ~ spl11_2
    | spl11_3
    | ~ spl11_86
    | ~ spl11_88
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f4095,f4113])).

fof(f4113,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | spl11_3
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f4112,f405])).

fof(f405,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f404,f142])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f139,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f63,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r1_tsep_1(sK8,sK6)
      | ~ r1_tsep_1(sK6,sK8) )
    & ( r1_tsep_1(sK8,sK7)
      | r1_tsep_1(sK7,sK8) )
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
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
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
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK5)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(sK6,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
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
            ( ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(sK6,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK6,X2)
            & m1_pre_topc(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK5)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK6)
            | ~ r1_tsep_1(sK6,X3) )
          & ( r1_tsep_1(X3,sK7)
            | r1_tsep_1(sK7,X3) )
          & m1_pre_topc(sK6,sK7)
          & m1_pre_topc(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK6)
          | ~ r1_tsep_1(sK6,X3) )
        & ( r1_tsep_1(X3,sK7)
          | r1_tsep_1(sK7,X3) )
        & m1_pre_topc(sK6,sK7)
        & m1_pre_topc(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ( ~ r1_tsep_1(sK8,sK6)
        | ~ r1_tsep_1(sK6,sK8) )
      & ( r1_tsep_1(sK8,sK7)
        | r1_tsep_1(sK7,sK8) )
      & m1_pre_topc(sK6,sK7)
      & m1_pre_topc(sK8,sK5)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
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
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f404,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | ~ l1_struct_0(sK8)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f398,f126])).

fof(f126,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_3
  <=> r1_tsep_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f398,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK8) ),
    inference(superposition,[],[f318,f145])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f318,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
      | r1_tsep_1(sK6,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f309,f140])).

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

fof(f65,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f309,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
      | r1_tsep_1(sK6,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(sK6) ) ),
    inference(superposition,[],[f75,f143])).

fof(f143,plain,(
    k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(resolution,[],[f140,f73])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f4112,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f3708,f142])).

fof(f3708,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ l1_struct_0(sK8)
    | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8))
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(superposition,[],[f3607,f145])).

fof(f3607,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
        | ~ l1_struct_0(X0)
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(duplicate_literal_removal,[],[f3598])).

fof(f3598,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6))
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))
        | ~ l1_struct_0(X0) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(resolution,[],[f3523,f3052])).

fof(f3052,plain,
    ( ! [X1] :
        ( ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
        | ~ l1_struct_0(X1) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f2945,f2505])).

fof(f2505,plain,
    ( l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
    | ~ spl11_103 ),
    inference(resolution,[],[f2504,f76])).

fof(f2504,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK6,sK6))
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f2489,f138])).

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

fof(f2489,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK6,sK6))
    | ~ l1_pre_topc(sK7)
    | ~ spl11_103 ),
    inference(resolution,[],[f2469,f92])).

fof(f2469,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)
    | ~ spl11_103 ),
    inference(avatar_component_clause,[],[f2468])).

fof(f2468,plain,
    ( spl11_103
  <=> m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).

fof(f2945,plain,
    ( ! [X1] :
        ( r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1))
        | ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) )
    | ~ spl11_86 ),
    inference(backward_demodulation,[],[f2376,f2174])).

fof(f2174,plain,
    ( k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))
    | ~ spl11_86 ),
    inference(avatar_component_clause,[],[f2172])).

fof(f2172,plain,
    ( spl11_86
  <=> k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f2376,plain,(
    ! [X1] :
      ( r1_xboole_0(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),u1_struct_0(X1))
      | ~ r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ) ),
    inference(superposition,[],[f74,f2368])).

fof(f2368,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2367,f2136])).

fof(f2136,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2135,f921])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f2135,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2134,f143])).

fof(f2134,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2130,f64])).

fof(f2130,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2076,f65])).

fof(f2076,plain,(
    ! [X8] :
      ( ~ m1_pre_topc(X8,sK5)
      | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6))
      | v2_struct_0(X8) ) ),
    inference(forward_demodulation,[],[f2075,f143])).

fof(f2075,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f2074,f61])).

fof(f2074,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f2073,f63])).

fof(f2073,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f2058,f64])).

fof(f2058,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f1519,f65])).

fof(f1519,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1518,f108])).

fof(f1518,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP4(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f1517,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1517,plain,(
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
    inference(subsumption_resolution,[],[f1516,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1516,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f2367,plain,(
    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2366,f143])).

fof(f2366,plain,(
    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2363,f64])).

fof(f2363,plain,
    ( k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2091,f70])).

fof(f70,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f2091,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(X12,sK7)
      | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6))
      | v2_struct_0(X12) ) ),
    inference(forward_demodulation,[],[f2090,f143])).

fof(f2090,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f2089,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f2089,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f2088,f138])).

fof(f2088,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f2062,f64])).

fof(f2062,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f1519,f70])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3523,plain,
    ( ! [X1] :
        ( r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(X1)
        | ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f3521,f2505])).

fof(f3521,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
        | ~ l1_struct_0(X1)
        | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(duplicate_literal_removal,[],[f3514])).

fof(f3514,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
        | ~ l1_struct_0(X1)
        | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1)
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(X1) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(resolution,[],[f3055,f98])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f3055,plain,
    ( ! [X4] :
        ( r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
        | ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6))
        | ~ l1_struct_0(X4) )
    | ~ spl11_86
    | ~ spl11_103 ),
    inference(subsumption_resolution,[],[f2948,f2505])).

fof(f2948,plain,
    ( ! [X4] :
        ( ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6))
        | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
        | ~ l1_struct_0(X4) )
    | ~ spl11_86 ),
    inference(backward_demodulation,[],[f2379,f2174])).

fof(f2379,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(u1_struct_0(X4),k2_struct_0(k1_tsep_1(sK5,sK6,sK6)))
      | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6))
      | ~ l1_struct_0(k1_tsep_1(sK7,sK6,sK6))
      | ~ l1_struct_0(X4) ) ),
    inference(superposition,[],[f75,f2368])).

fof(f4095,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ spl11_2
    | ~ spl11_88 ),
    inference(resolution,[],[f3919,f366])).

fof(f366,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f365,f141])).

fof(f141,plain,(
    l1_struct_0(sK7) ),
    inference(resolution,[],[f138,f76])).

fof(f365,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ l1_struct_0(sK7)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f362,f121])).

fof(f121,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl11_2
  <=> r1_tsep_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f362,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f183,f144])).

fof(f144,plain,(
    k2_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(resolution,[],[f141,f73])).

fof(f183,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | ~ r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f175,f142])).

fof(f175,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | ~ r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK8) ) ),
    inference(superposition,[],[f74,f145])).

fof(f3919,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k2_struct_0(sK7))
        | r1_xboole_0(X1,k2_struct_0(sK6)) )
    | ~ spl11_88 ),
    inference(backward_demodulation,[],[f2154,f2183])).

fof(f2183,plain,
    ( k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f2181])).

fof(f2181,plain,
    ( spl11_88
  <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f2154,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK5,sK7,sK6)))
      | r1_xboole_0(X1,k2_struct_0(sK6)) ) ),
    inference(superposition,[],[f104,f2139])).

fof(f2139,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2138,f1106])).

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

fof(f2138,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f2137,f144])).

fof(f2137,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f2131,f66])).

fof(f2131,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f2076,f67])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4106,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_contradiction_clause,[],[f4105])).

fof(f4105,plain,
    ( $false
    | ~ spl11_1
    | spl11_2 ),
    inference(subsumption_resolution,[],[f4104,f141])).

fof(f4104,plain,
    ( ~ l1_struct_0(sK7)
    | ~ spl11_1
    | spl11_2 ),
    inference(subsumption_resolution,[],[f4103,f142])).

fof(f4103,plain,
    ( ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK7)
    | ~ spl11_1
    | spl11_2 ),
    inference(subsumption_resolution,[],[f4102,f120])).

fof(f120,plain,
    ( ~ r1_tsep_1(sK8,sK7)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f4102,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK7)
    | ~ spl11_1 ),
    inference(resolution,[],[f117,f98])).

fof(f117,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl11_1
  <=> r1_tsep_1(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f4097,plain,
    ( ~ spl11_2
    | spl11_4
    | ~ spl11_88 ),
    inference(avatar_contradiction_clause,[],[f4096])).

fof(f4096,plain,
    ( $false
    | ~ spl11_2
    | spl11_4
    | ~ spl11_88 ),
    inference(subsumption_resolution,[],[f4095,f427])).

fof(f427,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | spl11_4 ),
    inference(subsumption_resolution,[],[f426,f140])).

fof(f426,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f422,f130])).

fof(f130,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl11_4
  <=> r1_tsep_1(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

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

fof(f3871,plain,(
    spl11_74 ),
    inference(avatar_contradiction_clause,[],[f3870])).

fof(f3870,plain,
    ( $false
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3869,f138])).

fof(f3869,plain,
    ( ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3868,f66])).

fof(f3868,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3867,f545])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f3867,plain,
    ( ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3866,f64])).

fof(f3866,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3865,f70])).

fof(f3865,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(duplicate_literal_removal,[],[f3864])).

fof(f3864,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_74 ),
    inference(resolution,[],[f3863,f108])).

fof(f3863,plain,
    ( ~ sP4(sK7,sK6,sK7)
    | spl11_74 ),
    inference(subsumption_resolution,[],[f3862,f138])).

fof(f3862,plain,
    ( ~ sP4(sK7,sK6,sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_74 ),
    inference(resolution,[],[f3853,f164])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

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

fof(f3853,plain,
    ( ~ sP2(k1_tsep_1(sK7,sK7,sK6),sK7)
    | spl11_74 ),
    inference(resolution,[],[f3831,f2008])).

fof(f2008,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | spl11_74 ),
    inference(avatar_component_clause,[],[f2007])).

fof(f2007,plain,
    ( spl11_74
  <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f3831,plain,(
    ! [X0] :
      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0))
      | ~ sP2(k1_tsep_1(sK7,sK7,sK6),X0) ) ),
    inference(superposition,[],[f79,f3819])).

fof(f3819,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f3818,f2371])).

fof(f2371,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f2370,f2139])).

fof(f2370,plain,(
    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f2369,f144])).

fof(f2369,plain,(
    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f2364,f66])).

fof(f2364,plain,
    ( k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f2091,f545])).

fof(f3818,plain,(
    u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f3813,f64])).

fof(f3813,plain,
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

fof(f2894,plain,(
    spl11_107 ),
    inference(avatar_contradiction_clause,[],[f2893])).

fof(f2893,plain,
    ( $false
    | spl11_107 ),
    inference(subsumption_resolution,[],[f2892,f137])).

fof(f2892,plain,
    ( ~ l1_pre_topc(sK6)
    | spl11_107 ),
    inference(subsumption_resolution,[],[f2891,f64])).

fof(f2891,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_107 ),
    inference(subsumption_resolution,[],[f2890,f543])).

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

fof(f2890,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_107 ),
    inference(duplicate_literal_removal,[],[f2889])).

fof(f2889,plain,
    ( ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_107 ),
    inference(resolution,[],[f2888,f108])).

fof(f2888,plain,
    ( ~ sP4(sK6,sK6,sK6)
    | spl11_107 ),
    inference(subsumption_resolution,[],[f2887,f137])).

fof(f2887,plain,
    ( ~ sP4(sK6,sK6,sK6)
    | ~ l1_pre_topc(sK6)
    | spl11_107 ),
    inference(resolution,[],[f2882,f164])).

fof(f2882,plain,
    ( ~ sP2(k1_tsep_1(sK6,sK6,sK6),sK6)
    | spl11_107 ),
    inference(resolution,[],[f2871,f2820])).

fof(f2820,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))
    | spl11_107 ),
    inference(avatar_component_clause,[],[f2818])).

fof(f2818,plain,
    ( spl11_107
  <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f2871,plain,(
    ! [X0] :
      ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(X0))
      | ~ sP2(k1_tsep_1(sK6,sK6,sK6),X0) ) ),
    inference(superposition,[],[f79,f2865])).

fof(f2865,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2864,f2565])).

fof(f2565,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2564,f2136])).

fof(f2564,plain,(
    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(forward_demodulation,[],[f2563,f143])).

fof(f2563,plain,(
    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2561,f64])).

fof(f2561,plain,
    ( k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f2087,f543])).

fof(f2087,plain,(
    ! [X11] :
      ( ~ m1_pre_topc(X11,sK6)
      | u1_struct_0(k1_tsep_1(sK6,X11,sK6)) = k2_xboole_0(u1_struct_0(X11),k2_struct_0(sK6))
      | v2_struct_0(X11) ) ),
    inference(forward_demodulation,[],[f2086,f143])).

fof(f2086,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f2085,f137])).

fof(f2085,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6) ) ),
    inference(subsumption_resolution,[],[f2068,f64])).

fof(f2068,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6) ) ),
    inference(duplicate_literal_removal,[],[f2061])).

fof(f2061,plain,(
    ! [X11] :
      ( k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X11,sK6)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f1519,f543])).

fof(f2864,plain,(
    u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6)) ),
    inference(subsumption_resolution,[],[f2862,f64])).

fof(f2862,plain,
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

fof(f2826,plain,
    ( spl11_88
    | ~ spl11_74 ),
    inference(avatar_split_clause,[],[f2153,f2007,f2181])).

fof(f2153,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(superposition,[],[f158,f2139])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2821,plain,
    ( spl11_86
    | ~ spl11_107 ),
    inference(avatar_split_clause,[],[f2145,f2818,f2172])).

fof(f2145,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))
    | k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) ),
    inference(superposition,[],[f158,f2136])).

fof(f2481,plain,(
    spl11_103 ),
    inference(avatar_contradiction_clause,[],[f2480])).

fof(f2480,plain,
    ( $false
    | spl11_103 ),
    inference(subsumption_resolution,[],[f2479,f66])).

fof(f2479,plain,
    ( v2_struct_0(sK7)
    | spl11_103 ),
    inference(subsumption_resolution,[],[f2478,f138])).

fof(f2478,plain,
    ( ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_103 ),
    inference(subsumption_resolution,[],[f2477,f64])).

fof(f2477,plain,
    ( v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_103 ),
    inference(subsumption_resolution,[],[f2476,f70])).

fof(f2476,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_103 ),
    inference(duplicate_literal_removal,[],[f2475])).

fof(f2475,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_103 ),
    inference(resolution,[],[f2474,f108])).

fof(f2474,plain,
    ( ~ sP4(sK7,sK6,sK6)
    | spl11_103 ),
    inference(resolution,[],[f2470,f107])).

fof(f2470,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)
    | spl11_103 ),
    inference(avatar_component_clause,[],[f2468])).

fof(f131,plain,
    ( ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f72,f128,f124])).

fof(f72,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f122,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f71,f119,f115])).

fof(f71,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (7545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (7545)Refutation not found, incomplete strategy% (7545)------------------------------
% 0.22/0.50  % (7545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (7552)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (7545)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7545)Memory used [KB]: 6268
% 0.22/0.51  % (7545)Time elapsed: 0.076 s
% 0.22/0.51  % (7545)------------------------------
% 0.22/0.51  % (7545)------------------------------
% 0.22/0.51  % (7541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (7546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (7550)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (7556)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (7542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (7543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (7532)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (7535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (7532)Refutation not found, incomplete strategy% (7532)------------------------------
% 0.22/0.53  % (7532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7532)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7532)Memory used [KB]: 10618
% 0.22/0.53  % (7532)Time elapsed: 0.103 s
% 0.22/0.53  % (7532)------------------------------
% 0.22/0.53  % (7532)------------------------------
% 0.22/0.53  % (7534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (7540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (7538)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (7553)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (7544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (7536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (7549)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (7539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (7555)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (7551)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (7548)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (7533)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (7547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (7554)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (7557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.02/0.63  % (7541)Refutation not found, incomplete strategy% (7541)------------------------------
% 2.02/0.63  % (7541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (7541)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.64  
% 2.02/0.64  % (7541)Memory used [KB]: 6140
% 2.02/0.64  % (7541)Time elapsed: 0.193 s
% 2.02/0.64  % (7541)------------------------------
% 2.02/0.64  % (7541)------------------------------
% 4.07/0.92  % (7557)Refutation found. Thanks to Tanya!
% 4.07/0.92  % SZS status Theorem for theBenchmark
% 4.07/0.92  % SZS output start Proof for theBenchmark
% 4.07/0.92  fof(f4123,plain,(
% 4.07/0.92    $false),
% 4.07/0.92    inference(avatar_sat_refutation,[],[f122,f131,f2481,f2821,f2826,f2894,f3871,f4097,f4106,f4122])).
% 4.07/0.92  fof(f4122,plain,(
% 4.07/0.92    ~spl11_2 | spl11_3 | ~spl11_86 | ~spl11_88 | ~spl11_103),
% 4.07/0.92    inference(avatar_contradiction_clause,[],[f4121])).
% 4.07/0.92  fof(f4121,plain,(
% 4.07/0.92    $false | (~spl11_2 | spl11_3 | ~spl11_86 | ~spl11_88 | ~spl11_103)),
% 4.07/0.92    inference(subsumption_resolution,[],[f4095,f4113])).
% 4.07/0.92  fof(f4113,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | (spl11_3 | ~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(subsumption_resolution,[],[f4112,f405])).
% 4.07/0.92  fof(f405,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | spl11_3),
% 4.07/0.92    inference(subsumption_resolution,[],[f404,f142])).
% 4.07/0.92  fof(f142,plain,(
% 4.07/0.92    l1_struct_0(sK8)),
% 4.07/0.92    inference(resolution,[],[f139,f76])).
% 4.07/0.92  fof(f76,plain,(
% 4.07/0.92    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f19])).
% 4.07/0.92  fof(f19,plain,(
% 4.07/0.92    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.07/0.92    inference(ennf_transformation,[],[f6])).
% 4.07/0.92  fof(f6,axiom,(
% 4.07/0.92    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 4.07/0.92  fof(f139,plain,(
% 4.07/0.92    l1_pre_topc(sK8)),
% 4.07/0.92    inference(subsumption_resolution,[],[f135,f63])).
% 4.07/0.92  fof(f63,plain,(
% 4.07/0.92    l1_pre_topc(sK5)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f42,plain,(
% 4.07/0.92    ((((~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & (r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 4.07/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f41,f40,f39,f38])).
% 4.07/0.92  fof(f38,plain,(
% 4.07/0.92    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 4.07/0.92    introduced(choice_axiom,[])).
% 4.07/0.92  fof(f39,plain,(
% 4.07/0.92    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6))),
% 4.07/0.92    introduced(choice_axiom,[])).
% 4.07/0.92  fof(f40,plain,(
% 4.07/0.92    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7))),
% 4.07/0.92    introduced(choice_axiom,[])).
% 4.07/0.92  fof(f41,plain,(
% 4.07/0.92    ? [X3] : ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & (r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) => ((~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & (r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8))),
% 4.07/0.92    introduced(choice_axiom,[])).
% 4.07/0.92  fof(f16,plain,(
% 4.07/0.92    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/0.92    inference(flattening,[],[f15])).
% 4.07/0.92  fof(f15,plain,(
% 4.07/0.92    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.07/0.92    inference(ennf_transformation,[],[f14])).
% 4.07/0.92  fof(f14,negated_conjecture,(
% 4.07/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 4.07/0.92    inference(negated_conjecture,[],[f13])).
% 4.07/0.92  fof(f13,conjecture,(
% 4.07/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 4.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 4.07/0.92  fof(f135,plain,(
% 4.07/0.92    l1_pre_topc(sK8) | ~l1_pre_topc(sK5)),
% 4.07/0.92    inference(resolution,[],[f92,f69])).
% 4.07/0.92  fof(f69,plain,(
% 4.07/0.92    m1_pre_topc(sK8,sK5)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f92,plain,(
% 4.07/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f21])).
% 4.07/0.92  fof(f21,plain,(
% 4.07/0.92    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.07/0.92    inference(ennf_transformation,[],[f7])).
% 4.07/0.92  fof(f7,axiom,(
% 4.07/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 4.07/0.92  fof(f404,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | ~l1_struct_0(sK8) | spl11_3),
% 4.07/0.92    inference(subsumption_resolution,[],[f398,f126])).
% 4.07/0.92  fof(f126,plain,(
% 4.07/0.92    ~r1_tsep_1(sK6,sK8) | spl11_3),
% 4.07/0.92    inference(avatar_component_clause,[],[f124])).
% 4.07/0.92  fof(f124,plain,(
% 4.07/0.92    spl11_3 <=> r1_tsep_1(sK6,sK8)),
% 4.07/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 4.07/0.92  fof(f398,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK8)),
% 4.07/0.92    inference(superposition,[],[f318,f145])).
% 4.07/0.92  fof(f145,plain,(
% 4.07/0.92    k2_struct_0(sK8) = u1_struct_0(sK8)),
% 4.07/0.92    inference(resolution,[],[f142,f73])).
% 4.07/0.92  fof(f73,plain,(
% 4.07/0.92    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f17])).
% 4.07/0.92  fof(f17,plain,(
% 4.07/0.92    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.07/0.92    inference(ennf_transformation,[],[f4])).
% 4.07/0.92  fof(f4,axiom,(
% 4.07/0.92    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 4.07/0.92  fof(f318,plain,(
% 4.07/0.92    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | r1_tsep_1(sK6,X1) | ~l1_struct_0(X1)) )),
% 4.07/0.92    inference(subsumption_resolution,[],[f309,f140])).
% 4.07/0.92  fof(f140,plain,(
% 4.07/0.92    l1_struct_0(sK6)),
% 4.07/0.92    inference(resolution,[],[f137,f76])).
% 4.07/0.92  fof(f137,plain,(
% 4.07/0.92    l1_pre_topc(sK6)),
% 4.07/0.92    inference(subsumption_resolution,[],[f133,f63])).
% 4.07/0.92  fof(f133,plain,(
% 4.07/0.92    l1_pre_topc(sK6) | ~l1_pre_topc(sK5)),
% 4.07/0.92    inference(resolution,[],[f92,f65])).
% 4.07/0.92  fof(f65,plain,(
% 4.07/0.92    m1_pre_topc(sK6,sK5)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f309,plain,(
% 4.07/0.92    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | r1_tsep_1(sK6,X1) | ~l1_struct_0(X1) | ~l1_struct_0(sK6)) )),
% 4.07/0.92    inference(superposition,[],[f75,f143])).
% 4.07/0.92  fof(f143,plain,(
% 4.07/0.92    k2_struct_0(sK6) = u1_struct_0(sK6)),
% 4.07/0.92    inference(resolution,[],[f140,f73])).
% 4.07/0.92  fof(f75,plain,(
% 4.07/0.92    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f43])).
% 4.07/0.92  fof(f43,plain,(
% 4.07/0.92    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.07/0.92    inference(nnf_transformation,[],[f18])).
% 4.07/0.92  fof(f18,plain,(
% 4.07/0.92    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.07/0.92    inference(ennf_transformation,[],[f9])).
% 4.07/0.92  fof(f9,axiom,(
% 4.07/0.92    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 4.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 4.07/0.92  fof(f4112,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | (~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(subsumption_resolution,[],[f3708,f142])).
% 4.07/0.92  fof(f3708,plain,(
% 4.07/0.92    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | ~l1_struct_0(sK8) | r1_xboole_0(k2_struct_0(sK6),k2_struct_0(sK8)) | (~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(superposition,[],[f3607,f145])).
% 4.07/0.92  fof(f3607,plain,(
% 4.07/0.92    ( ! [X0] : (~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) | ~l1_struct_0(X0) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0))) ) | (~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(duplicate_literal_removal,[],[f3598])).
% 4.07/0.92  fof(f3598,plain,(
% 4.07/0.92    ( ! [X0] : (~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),k2_struct_0(sK6)) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X0)) | ~l1_struct_0(X0)) ) | (~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(resolution,[],[f3523,f3052])).
% 4.07/0.92  fof(f3052,plain,(
% 4.07/0.92    ( ! [X1] : (~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | ~l1_struct_0(X1)) ) | (~spl11_86 | ~spl11_103)),
% 4.07/0.92    inference(subsumption_resolution,[],[f2945,f2505])).
% 4.07/0.92  fof(f2505,plain,(
% 4.07/0.92    l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~spl11_103),
% 4.07/0.92    inference(resolution,[],[f2504,f76])).
% 4.07/0.92  fof(f2504,plain,(
% 4.07/0.92    l1_pre_topc(k1_tsep_1(sK7,sK6,sK6)) | ~spl11_103),
% 4.07/0.92    inference(subsumption_resolution,[],[f2489,f138])).
% 4.07/0.92  fof(f138,plain,(
% 4.07/0.92    l1_pre_topc(sK7)),
% 4.07/0.92    inference(subsumption_resolution,[],[f134,f63])).
% 4.07/0.92  fof(f134,plain,(
% 4.07/0.92    l1_pre_topc(sK7) | ~l1_pre_topc(sK5)),
% 4.07/0.92    inference(resolution,[],[f92,f67])).
% 4.07/0.92  fof(f67,plain,(
% 4.07/0.92    m1_pre_topc(sK7,sK5)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f2489,plain,(
% 4.07/0.92    l1_pre_topc(k1_tsep_1(sK7,sK6,sK6)) | ~l1_pre_topc(sK7) | ~spl11_103),
% 4.07/0.92    inference(resolution,[],[f2469,f92])).
% 4.07/0.92  fof(f2469,plain,(
% 4.07/0.92    m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) | ~spl11_103),
% 4.07/0.92    inference(avatar_component_clause,[],[f2468])).
% 4.07/0.92  fof(f2468,plain,(
% 4.07/0.92    spl11_103 <=> m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7)),
% 4.07/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_103])])).
% 4.07/0.92  fof(f2945,plain,(
% 4.07/0.92    ( ! [X1] : (r1_xboole_0(k2_struct_0(sK6),u1_struct_0(X1)) | ~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) ) | ~spl11_86),
% 4.07/0.92    inference(backward_demodulation,[],[f2376,f2174])).
% 4.07/0.92  fof(f2174,plain,(
% 4.07/0.92    k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) | ~spl11_86),
% 4.07/0.92    inference(avatar_component_clause,[],[f2172])).
% 4.07/0.92  fof(f2172,plain,(
% 4.07/0.92    spl11_86 <=> k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 4.07/0.92    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).
% 4.07/0.92  fof(f2376,plain,(
% 4.07/0.92    ( ! [X1] : (r1_xboole_0(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),u1_struct_0(X1)) | ~r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) )),
% 4.07/0.92    inference(superposition,[],[f74,f2368])).
% 4.07/0.92  fof(f2368,plain,(
% 4.07/0.92    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 4.07/0.92    inference(forward_demodulation,[],[f2367,f2136])).
% 4.07/0.92  fof(f2136,plain,(
% 4.07/0.92    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6))),
% 4.07/0.92    inference(forward_demodulation,[],[f2135,f921])).
% 4.07/0.92  fof(f921,plain,(
% 4.07/0.92    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 4.07/0.92    inference(subsumption_resolution,[],[f917,f64])).
% 4.07/0.92  fof(f64,plain,(
% 4.07/0.92    ~v2_struct_0(sK6)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f917,plain,(
% 4.07/0.92    v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 4.07/0.92    inference(resolution,[],[f901,f65])).
% 4.07/0.92  fof(f901,plain,(
% 4.07/0.92    ( ! [X8] : (~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 4.07/0.92    inference(subsumption_resolution,[],[f900,f61])).
% 4.07/0.92  fof(f61,plain,(
% 4.07/0.92    ~v2_struct_0(sK5)),
% 4.07/0.92    inference(cnf_transformation,[],[f42])).
% 4.07/0.92  fof(f900,plain,(
% 4.07/0.92    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 4.07/0.92    inference(subsumption_resolution,[],[f899,f63])).
% 4.07/0.92  fof(f899,plain,(
% 4.07/0.92    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 4.07/0.92    inference(subsumption_resolution,[],[f885,f64])).
% 4.07/0.92  fof(f885,plain,(
% 4.07/0.92    ( ! [X8] : (v2_struct_0(X8) | ~m1_pre_topc(X8,sK5) | v2_struct_0(sK6) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK6,X8)) = u1_struct_0(k1_tsep_1(sK5,sK6,X8))) )),
% 4.07/0.92    inference(resolution,[],[f675,f65])).
% 4.07/0.92  fof(f675,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 4.07/0.92    inference(duplicate_literal_removal,[],[f674])).
% 4.07/0.92  fof(f674,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 4.07/0.92    inference(resolution,[],[f108,f449])).
% 4.07/0.92  fof(f449,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~l1_pre_topc(X0) | k2_struct_0(k1_tsep_1(X0,X2,X1)) = u1_struct_0(k1_tsep_1(X0,X2,X1))) )),
% 4.07/0.92    inference(resolution,[],[f448,f73])).
% 4.07/0.92  fof(f448,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (l1_struct_0(k1_tsep_1(X0,X2,X1)) | ~l1_pre_topc(X0) | ~sP4(X0,X1,X2)) )),
% 4.07/0.92    inference(resolution,[],[f165,f76])).
% 4.07/0.92  fof(f165,plain,(
% 4.07/0.92    ( ! [X4,X5,X3] : (l1_pre_topc(k1_tsep_1(X3,X5,X4)) | ~sP4(X3,X4,X5) | ~l1_pre_topc(X3)) )),
% 4.07/0.92    inference(resolution,[],[f107,f92])).
% 4.07/0.92  fof(f107,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f60])).
% 4.07/0.92  fof(f60,plain,(
% 4.07/0.92    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP4(X0,X1,X2))),
% 4.07/0.92    inference(rectify,[],[f59])).
% 4.07/0.92  fof(f59,plain,(
% 4.07/0.92    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 4.07/0.92    inference(nnf_transformation,[],[f36])).
% 4.07/0.92  fof(f36,plain,(
% 4.07/0.92    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 4.07/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 4.07/0.92  fof(f108,plain,(
% 4.07/0.92    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/0.92    inference(cnf_transformation,[],[f37])).
% 4.42/0.93  fof(f37,plain,(
% 4.42/0.93    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.42/0.93    inference(definition_folding,[],[f30,f36])).
% 4.42/0.93  fof(f30,plain,(
% 4.42/0.93    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.42/0.93    inference(flattening,[],[f29])).
% 4.42/0.93  fof(f29,plain,(
% 4.42/0.93    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.42/0.93    inference(ennf_transformation,[],[f10])).
% 4.42/0.93  fof(f10,axiom,(
% 4.42/0.93    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 4.42/0.93  fof(f2135,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2134,f143])).
% 4.42/0.93  fof(f2134,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2130,f64])).
% 4.42/0.93  fof(f2130,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) | v2_struct_0(sK6)),
% 4.42/0.93    inference(resolution,[],[f2076,f65])).
% 4.42/0.93  fof(f2076,plain,(
% 4.42/0.93    ( ! [X8] : (~m1_pre_topc(X8,sK5) | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6)) | v2_struct_0(X8)) )),
% 4.42/0.93    inference(forward_demodulation,[],[f2075,f143])).
% 4.42/0.93  fof(f2075,plain,(
% 4.42/0.93    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2074,f61])).
% 4.42/0.93  fof(f2074,plain,(
% 4.42/0.93    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | v2_struct_0(sK5)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2073,f63])).
% 4.42/0.93  fof(f2073,plain,(
% 4.42/0.93    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2058,f64])).
% 4.42/0.93  fof(f2058,plain,(
% 4.42/0.93    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 4.42/0.93    inference(resolution,[],[f1519,f65])).
% 4.42/0.93  fof(f1519,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f1518,f108])).
% 4.42/0.93  fof(f1518,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f1517,f105])).
% 4.42/0.93  fof(f105,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f60])).
% 4.42/0.93  fof(f1517,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f1516,f106])).
% 4.42/0.93  fof(f106,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f60])).
% 4.42/0.93  fof(f1516,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~v1_pre_topc(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.42/0.93    inference(resolution,[],[f110,f107])).
% 4.42/0.93  fof(f110,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.42/0.93    inference(equality_resolution,[],[f93])).
% 4.42/0.93  fof(f93,plain,(
% 4.42/0.93    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f55])).
% 4.42/0.93  fof(f55,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.42/0.93    inference(nnf_transformation,[],[f23])).
% 4.42/0.93  fof(f23,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.42/0.93    inference(flattening,[],[f22])).
% 4.42/0.93  fof(f22,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.42/0.93    inference(ennf_transformation,[],[f8])).
% 4.42/0.93  fof(f8,axiom,(
% 4.42/0.93    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 4.42/0.93  fof(f2367,plain,(
% 4.42/0.93    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2366,f143])).
% 4.42/0.93  fof(f2366,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2363,f64])).
% 4.42/0.93  fof(f2363,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | v2_struct_0(sK6)),
% 4.42/0.93    inference(resolution,[],[f2091,f70])).
% 4.42/0.93  fof(f70,plain,(
% 4.42/0.93    m1_pre_topc(sK6,sK7)),
% 4.42/0.93    inference(cnf_transformation,[],[f42])).
% 4.42/0.93  fof(f2091,plain,(
% 4.42/0.93    ( ! [X12] : (~m1_pre_topc(X12,sK7) | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6)) | v2_struct_0(X12)) )),
% 4.42/0.93    inference(forward_demodulation,[],[f2090,f143])).
% 4.42/0.93  fof(f2090,plain,(
% 4.42/0.93    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2089,f66])).
% 4.42/0.93  fof(f66,plain,(
% 4.42/0.93    ~v2_struct_0(sK7)),
% 4.42/0.93    inference(cnf_transformation,[],[f42])).
% 4.42/0.93  fof(f2089,plain,(
% 4.42/0.93    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | v2_struct_0(sK7)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2088,f138])).
% 4.42/0.93  fof(f2088,plain,(
% 4.42/0.93    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2062,f64])).
% 4.42/0.93  fof(f2062,plain,(
% 4.42/0.93    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 4.42/0.93    inference(resolution,[],[f1519,f70])).
% 4.42/0.93  fof(f74,plain,(
% 4.42/0.93    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f43])).
% 4.42/0.93  fof(f3523,plain,(
% 4.42/0.93    ( ! [X1] : (r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(X1) | ~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))) ) | (~spl11_86 | ~spl11_103)),
% 4.42/0.93    inference(subsumption_resolution,[],[f3521,f2505])).
% 4.42/0.93  fof(f3521,plain,(
% 4.42/0.93    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | ~l1_struct_0(X1) | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6))) ) | (~spl11_86 | ~spl11_103)),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f3514])).
% 4.42/0.93  fof(f3514,plain,(
% 4.42/0.93    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | ~l1_struct_0(X1) | r1_tsep_1(k1_tsep_1(sK7,sK6,sK6),X1) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X1)) ) | (~spl11_86 | ~spl11_103)),
% 4.42/0.93    inference(resolution,[],[f3055,f98])).
% 4.42/0.93  fof(f98,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f27])).
% 4.42/0.93  fof(f27,plain,(
% 4.42/0.93    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.42/0.93    inference(flattening,[],[f26])).
% 4.42/0.93  fof(f26,plain,(
% 4.42/0.93    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.42/0.93    inference(ennf_transformation,[],[f11])).
% 4.42/0.93  fof(f11,axiom,(
% 4.42/0.93    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 4.42/0.93  fof(f3055,plain,(
% 4.42/0.93    ( ! [X4] : (r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6)) | ~l1_struct_0(X4)) ) | (~spl11_86 | ~spl11_103)),
% 4.42/0.93    inference(subsumption_resolution,[],[f2948,f2505])).
% 4.42/0.93  fof(f2948,plain,(
% 4.42/0.93    ( ! [X4] : (~r1_xboole_0(u1_struct_0(X4),k2_struct_0(sK6)) | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X4)) ) | ~spl11_86),
% 4.42/0.93    inference(backward_demodulation,[],[f2379,f2174])).
% 4.42/0.93  fof(f2379,plain,(
% 4.42/0.93    ( ! [X4] : (~r1_xboole_0(u1_struct_0(X4),k2_struct_0(k1_tsep_1(sK5,sK6,sK6))) | r1_tsep_1(X4,k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(k1_tsep_1(sK7,sK6,sK6)) | ~l1_struct_0(X4)) )),
% 4.42/0.93    inference(superposition,[],[f75,f2368])).
% 4.42/0.93  fof(f4095,plain,(
% 4.42/0.93    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | (~spl11_2 | ~spl11_88)),
% 4.42/0.93    inference(resolution,[],[f3919,f366])).
% 4.42/0.93  fof(f366,plain,(
% 4.42/0.93    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~spl11_2),
% 4.42/0.93    inference(subsumption_resolution,[],[f365,f141])).
% 4.42/0.93  fof(f141,plain,(
% 4.42/0.93    l1_struct_0(sK7)),
% 4.42/0.93    inference(resolution,[],[f138,f76])).
% 4.42/0.93  fof(f365,plain,(
% 4.42/0.93    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~l1_struct_0(sK7) | ~spl11_2),
% 4.42/0.93    inference(subsumption_resolution,[],[f362,f121])).
% 4.42/0.93  fof(f121,plain,(
% 4.42/0.93    r1_tsep_1(sK8,sK7) | ~spl11_2),
% 4.42/0.93    inference(avatar_component_clause,[],[f119])).
% 4.42/0.93  fof(f119,plain,(
% 4.42/0.93    spl11_2 <=> r1_tsep_1(sK8,sK7)),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 4.42/0.93  fof(f362,plain,(
% 4.42/0.93    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK7)),
% 4.42/0.93    inference(superposition,[],[f183,f144])).
% 4.42/0.93  fof(f144,plain,(
% 4.42/0.93    k2_struct_0(sK7) = u1_struct_0(sK7)),
% 4.42/0.93    inference(resolution,[],[f141,f73])).
% 4.42/0.93  fof(f183,plain,(
% 4.42/0.93    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | ~r1_tsep_1(sK8,X3) | ~l1_struct_0(X3)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f175,f142])).
% 4.42/0.93  fof(f175,plain,(
% 4.42/0.93    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | ~r1_tsep_1(sK8,X3) | ~l1_struct_0(X3) | ~l1_struct_0(sK8)) )),
% 4.42/0.93    inference(superposition,[],[f74,f145])).
% 4.42/0.93  fof(f3919,plain,(
% 4.42/0.93    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(sK7)) | r1_xboole_0(X1,k2_struct_0(sK6))) ) | ~spl11_88),
% 4.42/0.93    inference(backward_demodulation,[],[f2154,f2183])).
% 4.42/0.93  fof(f2183,plain,(
% 4.42/0.93    k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~spl11_88),
% 4.42/0.93    inference(avatar_component_clause,[],[f2181])).
% 4.42/0.93  fof(f2181,plain,(
% 4.42/0.93    spl11_88 <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).
% 4.42/0.93  fof(f2154,plain,(
% 4.42/0.93    ( ! [X1] : (~r1_xboole_0(X1,k2_struct_0(k1_tsep_1(sK5,sK7,sK6))) | r1_xboole_0(X1,k2_struct_0(sK6))) )),
% 4.42/0.93    inference(superposition,[],[f104,f2139])).
% 4.42/0.93  fof(f2139,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2138,f1106])).
% 4.42/0.93  fof(f1106,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f1102,f64])).
% 4.42/0.93  fof(f1102,plain,(
% 4.42/0.93    v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.42/0.93    inference(resolution,[],[f904,f65])).
% 4.42/0.93  fof(f904,plain,(
% 4.42/0.93    ( ! [X9] : (~m1_pre_topc(X9,sK5) | v2_struct_0(X9) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f903,f61])).
% 4.42/0.93  fof(f903,plain,(
% 4.42/0.93    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f902,f63])).
% 4.42/0.93  fof(f902,plain,(
% 4.42/0.93    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f886,f66])).
% 4.42/0.93  fof(f886,plain,(
% 4.42/0.93    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.42/0.93    inference(resolution,[],[f675,f67])).
% 4.42/0.93  fof(f2138,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2137,f144])).
% 4.42/0.93  fof(f2137,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2131,f66])).
% 4.42/0.93  fof(f2131,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) | v2_struct_0(sK7)),
% 4.42/0.93    inference(resolution,[],[f2076,f67])).
% 4.42/0.93  fof(f104,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f28])).
% 4.42/0.93  fof(f28,plain,(
% 4.42/0.93    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.42/0.93    inference(ennf_transformation,[],[f2])).
% 4.42/0.93  fof(f2,axiom,(
% 4.42/0.93    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 4.42/0.93  fof(f4106,plain,(
% 4.42/0.93    ~spl11_1 | spl11_2),
% 4.42/0.93    inference(avatar_contradiction_clause,[],[f4105])).
% 4.42/0.93  fof(f4105,plain,(
% 4.42/0.93    $false | (~spl11_1 | spl11_2)),
% 4.42/0.93    inference(subsumption_resolution,[],[f4104,f141])).
% 4.42/0.93  fof(f4104,plain,(
% 4.42/0.93    ~l1_struct_0(sK7) | (~spl11_1 | spl11_2)),
% 4.42/0.93    inference(subsumption_resolution,[],[f4103,f142])).
% 4.42/0.93  fof(f4103,plain,(
% 4.42/0.93    ~l1_struct_0(sK8) | ~l1_struct_0(sK7) | (~spl11_1 | spl11_2)),
% 4.42/0.93    inference(subsumption_resolution,[],[f4102,f120])).
% 4.42/0.93  fof(f120,plain,(
% 4.42/0.93    ~r1_tsep_1(sK8,sK7) | spl11_2),
% 4.42/0.93    inference(avatar_component_clause,[],[f119])).
% 4.42/0.93  fof(f4102,plain,(
% 4.42/0.93    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK8) | ~l1_struct_0(sK7) | ~spl11_1),
% 4.42/0.93    inference(resolution,[],[f117,f98])).
% 4.42/0.93  fof(f117,plain,(
% 4.42/0.93    r1_tsep_1(sK7,sK8) | ~spl11_1),
% 4.42/0.93    inference(avatar_component_clause,[],[f115])).
% 4.42/0.93  fof(f115,plain,(
% 4.42/0.93    spl11_1 <=> r1_tsep_1(sK7,sK8)),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 4.42/0.93  fof(f4097,plain,(
% 4.42/0.93    ~spl11_2 | spl11_4 | ~spl11_88),
% 4.42/0.93    inference(avatar_contradiction_clause,[],[f4096])).
% 4.42/0.93  fof(f4096,plain,(
% 4.42/0.93    $false | (~spl11_2 | spl11_4 | ~spl11_88)),
% 4.42/0.93    inference(subsumption_resolution,[],[f4095,f427])).
% 4.42/0.93  fof(f427,plain,(
% 4.42/0.93    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | spl11_4),
% 4.42/0.93    inference(subsumption_resolution,[],[f426,f140])).
% 4.42/0.93  fof(f426,plain,(
% 4.42/0.93    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | ~l1_struct_0(sK6) | spl11_4),
% 4.42/0.93    inference(subsumption_resolution,[],[f422,f130])).
% 4.42/0.93  fof(f130,plain,(
% 4.42/0.93    ~r1_tsep_1(sK8,sK6) | spl11_4),
% 4.42/0.93    inference(avatar_component_clause,[],[f128])).
% 4.42/0.93  fof(f128,plain,(
% 4.42/0.93    spl11_4 <=> r1_tsep_1(sK8,sK6)),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 4.42/0.93  fof(f422,plain,(
% 4.42/0.93    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_tsep_1(sK8,sK6) | ~l1_struct_0(sK6)),
% 4.42/0.93    inference(superposition,[],[f320,f143])).
% 4.42/0.93  fof(f320,plain,(
% 4.42/0.93    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | r1_tsep_1(sK8,X3) | ~l1_struct_0(X3)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f311,f142])).
% 4.42/0.93  fof(f311,plain,(
% 4.42/0.93    ( ! [X3] : (~r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | r1_tsep_1(sK8,X3) | ~l1_struct_0(X3) | ~l1_struct_0(sK8)) )),
% 4.42/0.93    inference(superposition,[],[f75,f145])).
% 4.42/0.93  fof(f3871,plain,(
% 4.42/0.93    spl11_74),
% 4.42/0.93    inference(avatar_contradiction_clause,[],[f3870])).
% 4.42/0.93  fof(f3870,plain,(
% 4.42/0.93    $false | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3869,f138])).
% 4.42/0.93  fof(f3869,plain,(
% 4.42/0.93    ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3868,f66])).
% 4.42/0.93  fof(f3868,plain,(
% 4.42/0.93    v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3867,f545])).
% 4.42/0.93  fof(f545,plain,(
% 4.42/0.93    m1_pre_topc(sK7,sK7)),
% 4.42/0.93    inference(subsumption_resolution,[],[f544,f62])).
% 4.42/0.93  fof(f62,plain,(
% 4.42/0.93    v2_pre_topc(sK5)),
% 4.42/0.93    inference(cnf_transformation,[],[f42])).
% 4.42/0.93  fof(f544,plain,(
% 4.42/0.93    m1_pre_topc(sK7,sK7) | ~v2_pre_topc(sK5)),
% 4.42/0.93    inference(subsumption_resolution,[],[f538,f63])).
% 4.42/0.93  fof(f538,plain,(
% 4.42/0.93    m1_pre_topc(sK7,sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.42/0.93    inference(resolution,[],[f536,f67])).
% 4.42/0.93  fof(f536,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f527])).
% 4.42/0.93  fof(f527,plain,(
% 4.42/0.93    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 4.42/0.93    inference(resolution,[],[f95,f111])).
% 4.42/0.93  fof(f111,plain,(
% 4.42/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.42/0.93    inference(equality_resolution,[],[f100])).
% 4.42/0.93  fof(f100,plain,(
% 4.42/0.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.42/0.93    inference(cnf_transformation,[],[f58])).
% 4.42/0.93  fof(f58,plain,(
% 4.42/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.42/0.93    inference(flattening,[],[f57])).
% 4.42/0.93  fof(f57,plain,(
% 4.42/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.42/0.93    inference(nnf_transformation,[],[f1])).
% 4.42/0.93  fof(f1,axiom,(
% 4.42/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.42/0.93  fof(f95,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f56])).
% 4.42/0.93  fof(f56,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.42/0.93    inference(nnf_transformation,[],[f25])).
% 4.42/0.93  fof(f25,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.42/0.93    inference(flattening,[],[f24])).
% 4.42/0.93  fof(f24,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.42/0.93    inference(ennf_transformation,[],[f12])).
% 4.42/0.93  fof(f12,axiom,(
% 4.42/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 4.42/0.93  fof(f3867,plain,(
% 4.42/0.93    ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3866,f64])).
% 4.42/0.93  fof(f3866,plain,(
% 4.42/0.93    v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3865,f70])).
% 4.42/0.93  fof(f3865,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f3864])).
% 4.42/0.93  fof(f3864,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_74),
% 4.42/0.93    inference(resolution,[],[f3863,f108])).
% 4.42/0.93  fof(f3863,plain,(
% 4.42/0.93    ~sP4(sK7,sK6,sK7) | spl11_74),
% 4.42/0.93    inference(subsumption_resolution,[],[f3862,f138])).
% 4.42/0.93  fof(f3862,plain,(
% 4.42/0.93    ~sP4(sK7,sK6,sK7) | ~l1_pre_topc(sK7) | spl11_74),
% 4.42/0.93    inference(resolution,[],[f3853,f164])).
% 4.42/0.93  fof(f164,plain,(
% 4.42/0.93    ( ! [X2,X0,X1] : (sP2(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2) | ~l1_pre_topc(X0)) )),
% 4.42/0.93    inference(resolution,[],[f107,f147])).
% 4.42/0.93  fof(f147,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X1)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f146,f92])).
% 4.42/0.93  fof(f146,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 4.42/0.93    inference(resolution,[],[f77,f91])).
% 4.42/0.93  fof(f91,plain,(
% 4.42/0.93    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f35])).
% 4.42/0.93  fof(f35,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : (sP3(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.42/0.93    inference(definition_folding,[],[f20,f34,f33,f32,f31])).
% 4.42/0.93  fof(f31,plain,(
% 4.42/0.93    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.42/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.42/0.93  fof(f32,plain,(
% 4.42/0.93    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> sP0(X2,X1,X0)))),
% 4.42/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.42/0.93  fof(f33,plain,(
% 4.42/0.93    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 4.42/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 4.42/0.93  fof(f34,plain,(
% 4.42/0.93    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 4.42/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 4.42/0.93  fof(f20,plain,(
% 4.42/0.93    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.42/0.93    inference(ennf_transformation,[],[f5])).
% 4.42/0.93  fof(f5,axiom,(
% 4.42/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 4.42/0.93  fof(f77,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~sP3(X0,X1) | ~m1_pre_topc(X1,X0) | sP2(X1,X0)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f44])).
% 4.42/0.93  fof(f44,plain,(
% 4.42/0.93    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP3(X0,X1))),
% 4.42/0.93    inference(nnf_transformation,[],[f34])).
% 4.42/0.93  fof(f3853,plain,(
% 4.42/0.93    ~sP2(k1_tsep_1(sK7,sK7,sK6),sK7) | spl11_74),
% 4.42/0.93    inference(resolution,[],[f3831,f2008])).
% 4.42/0.93  fof(f2008,plain,(
% 4.42/0.93    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | spl11_74),
% 4.42/0.93    inference(avatar_component_clause,[],[f2007])).
% 4.42/0.93  fof(f2007,plain,(
% 4.42/0.93    spl11_74 <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).
% 4.42/0.93  fof(f3831,plain,(
% 4.42/0.93    ( ! [X0] : (r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0)) | ~sP2(k1_tsep_1(sK7,sK7,sK6),X0)) )),
% 4.42/0.93    inference(superposition,[],[f79,f3819])).
% 4.42/0.93  fof(f3819,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f3818,f2371])).
% 4.42/0.93  fof(f2371,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2370,f2139])).
% 4.42/0.93  fof(f2370,plain,(
% 4.42/0.93    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2369,f144])).
% 4.42/0.93  fof(f2369,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2364,f66])).
% 4.42/0.93  fof(f2364,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(sK7)),
% 4.42/0.93    inference(resolution,[],[f2091,f545])).
% 4.42/0.93  fof(f3818,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f3813,f64])).
% 4.42/0.93  fof(f3813,plain,(
% 4.42/0.93    v2_struct_0(sK6) | u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.42/0.93    inference(resolution,[],[f914,f70])).
% 4.42/0.93  fof(f914,plain,(
% 4.42/0.93    ( ! [X13] : (~m1_pre_topc(X13,sK7) | v2_struct_0(X13) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f913,f138])).
% 4.42/0.93  fof(f913,plain,(
% 4.42/0.93    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | ~l1_pre_topc(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f893,f66])).
% 4.42/0.93  fof(f893,plain,(
% 4.42/0.93    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f890])).
% 4.42/0.93  fof(f890,plain,(
% 4.42/0.93    ( ! [X13] : (v2_struct_0(X13) | ~m1_pre_topc(X13,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | k2_struct_0(k1_tsep_1(sK7,sK7,X13)) = u1_struct_0(k1_tsep_1(sK7,sK7,X13))) )),
% 4.42/0.93    inference(resolution,[],[f675,f545])).
% 4.42/0.93  fof(f79,plain,(
% 4.42/0.93    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP2(X0,X1)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f49])).
% 4.42/0.93  fof(f49,plain,(
% 4.42/0.93    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 4.42/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 4.42/0.93  fof(f48,plain,(
% 4.42/0.93    ! [X1,X0] : (? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.42/0.93    introduced(choice_axiom,[])).
% 4.42/0.93  fof(f47,plain,(
% 4.42/0.93    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 4.42/0.93    inference(rectify,[],[f46])).
% 4.42/0.93  fof(f46,plain,(
% 4.42/0.93    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 4.42/0.93    inference(flattening,[],[f45])).
% 4.42/0.93  fof(f45,plain,(
% 4.42/0.93    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 4.42/0.93    inference(nnf_transformation,[],[f33])).
% 4.42/0.93  fof(f2894,plain,(
% 4.42/0.93    spl11_107),
% 4.42/0.93    inference(avatar_contradiction_clause,[],[f2893])).
% 4.42/0.93  fof(f2893,plain,(
% 4.42/0.93    $false | spl11_107),
% 4.42/0.93    inference(subsumption_resolution,[],[f2892,f137])).
% 4.42/0.93  fof(f2892,plain,(
% 4.42/0.93    ~l1_pre_topc(sK6) | spl11_107),
% 4.42/0.93    inference(subsumption_resolution,[],[f2891,f64])).
% 4.42/0.93  fof(f2891,plain,(
% 4.42/0.93    v2_struct_0(sK6) | ~l1_pre_topc(sK6) | spl11_107),
% 4.42/0.93    inference(subsumption_resolution,[],[f2890,f543])).
% 4.42/0.93  fof(f543,plain,(
% 4.42/0.93    m1_pre_topc(sK6,sK6)),
% 4.42/0.93    inference(subsumption_resolution,[],[f542,f62])).
% 4.42/0.93  fof(f542,plain,(
% 4.42/0.93    m1_pre_topc(sK6,sK6) | ~v2_pre_topc(sK5)),
% 4.42/0.93    inference(subsumption_resolution,[],[f537,f63])).
% 4.42/0.93  fof(f537,plain,(
% 4.42/0.93    m1_pre_topc(sK6,sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.42/0.93    inference(resolution,[],[f536,f65])).
% 4.42/0.93  fof(f2890,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | spl11_107),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f2889])).
% 4.42/0.93  fof(f2889,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | v2_struct_0(sK6) | spl11_107),
% 4.42/0.93    inference(resolution,[],[f2888,f108])).
% 4.42/0.93  fof(f2888,plain,(
% 4.42/0.93    ~sP4(sK6,sK6,sK6) | spl11_107),
% 4.42/0.93    inference(subsumption_resolution,[],[f2887,f137])).
% 4.42/0.93  fof(f2887,plain,(
% 4.42/0.93    ~sP4(sK6,sK6,sK6) | ~l1_pre_topc(sK6) | spl11_107),
% 4.42/0.93    inference(resolution,[],[f2882,f164])).
% 4.42/0.93  fof(f2882,plain,(
% 4.42/0.93    ~sP2(k1_tsep_1(sK6,sK6,sK6),sK6) | spl11_107),
% 4.42/0.93    inference(resolution,[],[f2871,f2820])).
% 4.42/0.93  fof(f2820,plain,(
% 4.42/0.93    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) | spl11_107),
% 4.42/0.93    inference(avatar_component_clause,[],[f2818])).
% 4.42/0.93  fof(f2818,plain,(
% 4.42/0.93    spl11_107 <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6))),
% 4.42/0.93    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).
% 4.42/0.93  fof(f2871,plain,(
% 4.42/0.93    ( ! [X0] : (r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(X0)) | ~sP2(k1_tsep_1(sK6,sK6,sK6),X0)) )),
% 4.42/0.93    inference(superposition,[],[f79,f2865])).
% 4.42/0.93  fof(f2865,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2864,f2565])).
% 4.42/0.93  fof(f2565,plain,(
% 4.42/0.93    k2_struct_0(k1_tsep_1(sK5,sK6,sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2564,f2136])).
% 4.42/0.93  fof(f2564,plain,(
% 4.42/0.93    k2_xboole_0(k2_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(forward_demodulation,[],[f2563,f143])).
% 4.42/0.93  fof(f2563,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2561,f64])).
% 4.42/0.93  fof(f2561,plain,(
% 4.42/0.93    k2_xboole_0(u1_struct_0(sK6),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) | v2_struct_0(sK6)),
% 4.42/0.93    inference(resolution,[],[f2087,f543])).
% 4.42/0.93  fof(f2087,plain,(
% 4.42/0.93    ( ! [X11] : (~m1_pre_topc(X11,sK6) | u1_struct_0(k1_tsep_1(sK6,X11,sK6)) = k2_xboole_0(u1_struct_0(X11),k2_struct_0(sK6)) | v2_struct_0(X11)) )),
% 4.42/0.93    inference(forward_demodulation,[],[f2086,f143])).
% 4.42/0.93  fof(f2086,plain,(
% 4.42/0.93    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2085,f137])).
% 4.42/0.93  fof(f2085,plain,(
% 4.42/0.93    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6)) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f2068,f64])).
% 4.42/0.93  fof(f2068,plain,(
% 4.42/0.93    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6)) )),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f2061])).
% 4.42/0.93  fof(f2061,plain,(
% 4.42/0.93    ( ! [X11] : (k2_xboole_0(u1_struct_0(X11),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK6,X11,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | ~l1_pre_topc(sK6) | v2_struct_0(sK6)) )),
% 4.42/0.93    inference(resolution,[],[f1519,f543])).
% 4.42/0.93  fof(f2864,plain,(
% 4.42/0.93    u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(subsumption_resolution,[],[f2862,f64])).
% 4.42/0.93  fof(f2862,plain,(
% 4.42/0.93    v2_struct_0(sK6) | u1_struct_0(k1_tsep_1(sK6,sK6,sK6)) = k2_struct_0(k1_tsep_1(sK6,sK6,sK6))),
% 4.42/0.93    inference(resolution,[],[f909,f543])).
% 4.42/0.93  fof(f909,plain,(
% 4.42/0.93    ( ! [X11] : (~m1_pre_topc(X11,sK6) | v2_struct_0(X11) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f908,f137])).
% 4.42/0.93  fof(f908,plain,(
% 4.42/0.93    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | ~l1_pre_topc(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 4.42/0.93    inference(subsumption_resolution,[],[f894,f64])).
% 4.42/0.93  fof(f894,plain,(
% 4.42/0.93    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f888])).
% 4.42/0.93  fof(f888,plain,(
% 4.42/0.93    ( ! [X11] : (v2_struct_0(X11) | ~m1_pre_topc(X11,sK6) | v2_struct_0(sK6) | ~l1_pre_topc(sK6) | v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK6,sK6,X11)) = u1_struct_0(k1_tsep_1(sK6,sK6,X11))) )),
% 4.42/0.93    inference(resolution,[],[f675,f543])).
% 4.42/0.93  fof(f2826,plain,(
% 4.42/0.93    spl11_88 | ~spl11_74),
% 4.42/0.93    inference(avatar_split_clause,[],[f2153,f2007,f2181])).
% 4.42/0.93  fof(f2153,plain,(
% 4.42/0.93    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.42/0.93    inference(superposition,[],[f158,f2139])).
% 4.42/0.93  fof(f158,plain,(
% 4.42/0.93    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 4.42/0.93    inference(resolution,[],[f101,f97])).
% 4.42/0.93  fof(f97,plain,(
% 4.42/0.93    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.42/0.93    inference(cnf_transformation,[],[f3])).
% 4.42/0.93  fof(f3,axiom,(
% 4.42/0.93    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.42/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.42/0.93  fof(f101,plain,(
% 4.42/0.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.42/0.93    inference(cnf_transformation,[],[f58])).
% 4.42/0.93  fof(f2821,plain,(
% 4.42/0.93    spl11_86 | ~spl11_107),
% 4.42/0.93    inference(avatar_split_clause,[],[f2145,f2818,f2172])).
% 4.42/0.93  fof(f2145,plain,(
% 4.42/0.93    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK6,sK6)),k2_struct_0(sK6)) | k2_struct_0(sK6) = k2_struct_0(k1_tsep_1(sK5,sK6,sK6))),
% 4.42/0.93    inference(superposition,[],[f158,f2136])).
% 4.42/0.93  fof(f2481,plain,(
% 4.42/0.93    spl11_103),
% 4.42/0.93    inference(avatar_contradiction_clause,[],[f2480])).
% 4.42/0.93  fof(f2480,plain,(
% 4.42/0.93    $false | spl11_103),
% 4.42/0.93    inference(subsumption_resolution,[],[f2479,f66])).
% 4.42/0.93  fof(f2479,plain,(
% 4.42/0.93    v2_struct_0(sK7) | spl11_103),
% 4.42/0.93    inference(subsumption_resolution,[],[f2478,f138])).
% 4.42/0.93  fof(f2478,plain,(
% 4.42/0.93    ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_103),
% 4.42/0.93    inference(subsumption_resolution,[],[f2477,f64])).
% 4.42/0.93  fof(f2477,plain,(
% 4.42/0.93    v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_103),
% 4.42/0.93    inference(subsumption_resolution,[],[f2476,f70])).
% 4.42/0.93  fof(f2476,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_103),
% 4.42/0.93    inference(duplicate_literal_removal,[],[f2475])).
% 4.42/0.93  fof(f2475,plain,(
% 4.42/0.93    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_103),
% 4.42/0.93    inference(resolution,[],[f2474,f108])).
% 4.42/0.93  fof(f2474,plain,(
% 4.42/0.93    ~sP4(sK7,sK6,sK6) | spl11_103),
% 4.42/0.93    inference(resolution,[],[f2470,f107])).
% 4.42/0.93  fof(f2470,plain,(
% 4.42/0.93    ~m1_pre_topc(k1_tsep_1(sK7,sK6,sK6),sK7) | spl11_103),
% 4.42/0.93    inference(avatar_component_clause,[],[f2468])).
% 4.42/0.93  fof(f131,plain,(
% 4.42/0.93    ~spl11_3 | ~spl11_4),
% 4.42/0.93    inference(avatar_split_clause,[],[f72,f128,f124])).
% 4.42/0.93  fof(f72,plain,(
% 4.42/0.93    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 4.42/0.93    inference(cnf_transformation,[],[f42])).
% 4.42/0.93  fof(f122,plain,(
% 4.42/0.93    spl11_1 | spl11_2),
% 4.42/0.93    inference(avatar_split_clause,[],[f71,f119,f115])).
% 4.42/0.93  fof(f71,plain,(
% 4.42/0.93    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 4.42/0.93    inference(cnf_transformation,[],[f42])).
% 4.42/0.93  % SZS output end Proof for theBenchmark
% 4.42/0.93  % (7557)------------------------------
% 4.42/0.93  % (7557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.93  % (7557)Termination reason: Refutation
% 4.42/0.93  
% 4.42/0.93  % (7557)Memory used [KB]: 14328
% 4.42/0.93  % (7557)Time elapsed: 0.489 s
% 4.42/0.93  % (7557)------------------------------
% 4.42/0.93  % (7557)------------------------------
% 4.42/0.93  % (7531)Success in time 0.564 s
%------------------------------------------------------------------------------

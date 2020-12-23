%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:54 EST 2020

% Result     : Theorem 4.82s
% Output     : Refutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  213 (1726 expanded)
%              Number of leaves         :   31 ( 664 expanded)
%              Depth                    :   25
%              Number of atoms          :  867 (18215 expanded)
%              Number of equality atoms :   66 ( 225 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5397,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f132,f1593,f1598,f3309,f5102,f5106,f5383,f5396])).

% (4179)Time limit reached!
% (4179)------------------------------
% (4179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5396,plain,
    ( spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f5395])).

fof(f5395,plain,
    ( $false
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f5394,f143])).

fof(f143,plain,(
    l1_struct_0(sK8) ),
    inference(resolution,[],[f140,f77])).

fof(f77,plain,(
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

fof(f140,plain,(
    l1_pre_topc(sK8) ),
    inference(subsumption_resolution,[],[f136,f64])).

fof(f64,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f42,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f136,plain,
    ( l1_pre_topc(sK8)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f93,f70])).

fof(f70,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
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

fof(f5394,plain,
    ( ~ l1_struct_0(sK8)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f5393,f142])).

fof(f142,plain,(
    l1_struct_0(sK7) ),
    inference(resolution,[],[f139,f77])).

fof(f139,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f93,f68])).

fof(f68,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f5393,plain,
    ( ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f5392,f126])).

fof(f126,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl11_3
  <=> r1_tsep_1(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f5392,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK8)
    | ~ spl11_4 ),
    inference(resolution,[],[f131,f98])).

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

fof(f131,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl11_4
  <=> r1_tsep_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f5383,plain,
    ( ~ spl11_3
    | spl11_27
    | ~ spl11_121 ),
    inference(avatar_contradiction_clause,[],[f5382])).

fof(f5382,plain,
    ( $false
    | ~ spl11_3
    | spl11_27
    | ~ spl11_121 ),
    inference(subsumption_resolution,[],[f5381,f381])).

fof(f381,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | spl11_27 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl11_27
  <=> r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f5381,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | ~ spl11_3
    | ~ spl11_121 ),
    inference(resolution,[],[f5153,f377])).

fof(f377,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f376,f142])).

fof(f376,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ l1_struct_0(sK7)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f373,f169])).

fof(f169,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f168,f142])).

fof(f168,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f167,f143])).

fof(f167,plain,
    ( r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK8)
    | ~ l1_struct_0(sK7)
    | ~ spl11_3 ),
    inference(resolution,[],[f98,f127])).

fof(f127,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f373,plain,
    ( r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7))
    | ~ r1_tsep_1(sK8,sK7)
    | ~ l1_struct_0(sK7) ),
    inference(superposition,[],[f194,f145])).

fof(f145,plain,(
    k2_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(resolution,[],[f142,f74])).

fof(f74,plain,(
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

fof(f194,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | ~ r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f186,f143])).

fof(f186,plain,(
    ! [X3] :
      ( r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3))
      | ~ r1_tsep_1(sK8,X3)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK8) ) ),
    inference(superposition,[],[f75,f146])).

fof(f146,plain,(
    k2_struct_0(sK8) = u1_struct_0(sK8) ),
    inference(resolution,[],[f143,f74])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f5153,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,k2_struct_0(sK7))
        | r1_xboole_0(X2,k2_struct_0(sK6)) )
    | ~ spl11_121 ),
    inference(backward_demodulation,[],[f1968,f3503])).

fof(f3503,plain,
    ( k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))
    | ~ spl11_121 ),
    inference(avatar_component_clause,[],[f3501])).

fof(f3501,plain,
    ( spl11_121
  <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).

fof(f1968,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k2_struct_0(k1_tsep_1(sK5,sK7,sK6)))
      | r1_xboole_0(X2,k2_struct_0(sK6)) ) ),
    inference(superposition,[],[f104,f1939])).

fof(f1939,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f1938,f1127])).

fof(f1127,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f1123,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f1123,plain,
    ( v2_struct_0(sK6)
    | k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(resolution,[],[f909,f66])).

fof(f66,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f909,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(X9)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f908,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f908,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f907,f64])).

fof(f907,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(subsumption_resolution,[],[f891,f67])).

% (4179)Termination reason: Time limit
fof(f67,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f43])).

% (4179)Termination phase: Saturation
fof(f891,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ m1_pre_topc(X9,sK5)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5)
      | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9)) ) ),
    inference(resolution,[],[f776,f68])).

% (4179)Memory used [KB]: 15095
fof(f776,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0)) ) ),
    inference(duplicate_literal_removal,[],[f775])).

% (4179)Time elapsed: 0.606 s
% (4179)------------------------------
% (4179)------------------------------
fof(f775,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0)) ) ),
    inference(resolution,[],[f109,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(k1_tsep_1(X0,X2,X1)) = u1_struct_0(k1_tsep_1(X0,X2,X1)) ) ),
    inference(resolution,[],[f179,f74])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( l1_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ l1_pre_topc(X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f172,f77])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( l1_pre_topc(k1_tsep_1(X3,X5,X4))
      | ~ sP4(X3,X4,X5)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f108,f93])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f37])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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

fof(f1938,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f1937,f145])).

fof(f1937,plain,(
    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1931,f67])).

fof(f1931,plain,
    ( u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f1900,f68])).

fof(f1900,plain,(
    ! [X8] :
      ( ~ m1_pre_topc(X8,sK5)
      | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6))
      | v2_struct_0(X8) ) ),
    inference(forward_demodulation,[],[f1899,f144])).

fof(f144,plain,(
    k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(resolution,[],[f141,f74])).

fof(f141,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f138,f77])).

fof(f138,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f134,f64])).

fof(f134,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f93,f66])).

fof(f1899,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f1898,f62])).

fof(f1898,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f1897,f64])).

fof(f1897,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f1881,f65])).

fof(f1881,plain,(
    ! [X8] :
      ( k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X8,sK5)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f1579,f66])).

fof(f1579,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1578,f109])).

fof(f1578,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1))
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ sP4(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f1577,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1577,plain,(
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
    inference(subsumption_resolution,[],[f1576,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1576,plain,(
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
    inference(resolution,[],[f111,f108])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f5106,plain,
    ( spl11_74
    | ~ spl11_99 ),
    inference(avatar_contradiction_clause,[],[f5105])).

fof(f5105,plain,
    ( $false
    | spl11_74
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f5103,f3333])).

fof(f3333,plain,
    ( sP2(k1_tsep_1(sK7,sK7,sK6),sK7)
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f3316,f139])).

fof(f3316,plain,
    ( sP2(k1_tsep_1(sK7,sK7,sK6),sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl11_99 ),
    inference(resolution,[],[f3298,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP2(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | sP2(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f35,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & r2_hidden(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> sP0(X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( ! [X2] :
            ( sP1(X0,X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
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

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f3298,plain,
    ( m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)
    | ~ spl11_99 ),
    inference(avatar_component_clause,[],[f3297])).

fof(f3297,plain,
    ( spl11_99
  <=> m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f5103,plain,
    ( ~ sP2(k1_tsep_1(sK7,sK7,sK6),sK7)
    | spl11_74
    | ~ spl11_99 ),
    inference(resolution,[],[f1817,f3364])).

fof(f3364,plain,
    ( ! [X0] :
        ( r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0))
        | ~ sP2(k1_tsep_1(sK7,sK7,sK6),X0) )
    | ~ spl11_99 ),
    inference(superposition,[],[f80,f3337])).

fof(f3337,plain,
    ( k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ spl11_99 ),
    inference(forward_demodulation,[],[f3336,f2824])).

fof(f2824,plain,(
    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(forward_demodulation,[],[f2823,f1939])).

fof(f2823,plain,(
    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(backward_demodulation,[],[f2639,f145])).

fof(f2639,plain,(
    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) ),
    inference(subsumption_resolution,[],[f2633,f67])).

fof(f2633,plain,
    ( k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f1915,f560])).

fof(f560,plain,(
    m1_pre_topc(sK7,sK7) ),
    inference(subsumption_resolution,[],[f559,f63])).

fof(f63,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f559,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f553,f64])).

fof(f553,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f551,f68])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f96,f112])).

fof(f112,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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

fof(f1915,plain,(
    ! [X12] :
      ( ~ m1_pre_topc(X12,sK7)
      | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6))
      | v2_struct_0(X12) ) ),
    inference(forward_demodulation,[],[f1914,f144])).

fof(f1914,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f1913,f67])).

fof(f1913,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1912,f139])).

fof(f1912,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1885,f65])).

fof(f1885,plain,(
    ! [X12] :
      ( k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6))
      | v2_struct_0(sK6)
      | ~ m1_pre_topc(X12,sK7)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f1579,f71])).

fof(f71,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f3336,plain,
    ( u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ spl11_99 ),
    inference(resolution,[],[f3335,f74])).

fof(f3335,plain,
    ( l1_struct_0(k1_tsep_1(sK7,sK7,sK6))
    | ~ spl11_99 ),
    inference(resolution,[],[f3334,f77])).

fof(f3334,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK7,sK6))
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f3317,f139])).

fof(f3317,plain,
    ( l1_pre_topc(k1_tsep_1(sK7,sK7,sK6))
    | ~ l1_pre_topc(sK7)
    | ~ spl11_99 ),
    inference(resolution,[],[f3298,f93])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP1(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP1(X1,X0,sK9(X0,X1))
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(nnf_transformation,[],[f34])).

fof(f1817,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | spl11_74 ),
    inference(avatar_component_clause,[],[f1816])).

fof(f1816,plain,
    ( spl11_74
  <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f5102,plain,
    ( spl11_121
    | ~ spl11_74 ),
    inference(avatar_split_clause,[],[f1973,f1816,f3501])).

fof(f1973,plain,
    ( ~ r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))
    | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) ),
    inference(superposition,[],[f162,f1939])).

fof(f162,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f101,f147])).

fof(f147,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f105,f112])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f3309,plain,(
    spl11_99 ),
    inference(avatar_contradiction_clause,[],[f3308])).

fof(f3308,plain,
    ( $false
    | spl11_99 ),
    inference(subsumption_resolution,[],[f3307,f139])).

fof(f3307,plain,
    ( ~ l1_pre_topc(sK7)
    | spl11_99 ),
    inference(subsumption_resolution,[],[f3306,f67])).

fof(f3306,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_99 ),
    inference(subsumption_resolution,[],[f3305,f560])).

fof(f3305,plain,
    ( ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_99 ),
    inference(subsumption_resolution,[],[f3304,f65])).

fof(f3304,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_99 ),
    inference(subsumption_resolution,[],[f3303,f71])).

fof(f3303,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl11_99 ),
    inference(duplicate_literal_removal,[],[f3302])).

fof(f3302,plain,
    ( ~ m1_pre_topc(sK6,sK7)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK7,sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | v2_struct_0(sK7)
    | spl11_99 ),
    inference(resolution,[],[f3301,f109])).

fof(f3301,plain,
    ( ~ sP4(sK7,sK6,sK7)
    | spl11_99 ),
    inference(resolution,[],[f3299,f108])).

fof(f3299,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)
    | spl11_99 ),
    inference(avatar_component_clause,[],[f3297])).

fof(f1598,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1596,f143])).

fof(f1596,plain,
    ( ~ l1_struct_0(sK8)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1595,f141])).

fof(f1595,plain,
    ( ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1594,f118])).

fof(f118,plain,
    ( ~ r1_tsep_1(sK6,sK8)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl11_1
  <=> r1_tsep_1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1594,plain,
    ( r1_tsep_1(sK6,sK8)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK8)
    | ~ spl11_2 ),
    inference(resolution,[],[f121,f98])).

fof(f121,plain,
    ( r1_tsep_1(sK8,sK6)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl11_2
  <=> r1_tsep_1(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1593,plain,
    ( spl11_2
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f1375,f380,f120])).

fof(f1375,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | r1_tsep_1(sK8,sK6) ),
    inference(subsumption_resolution,[],[f445,f143])).

fof(f445,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))
    | r1_tsep_1(sK8,sK6)
    | ~ l1_struct_0(sK8) ),
    inference(superposition,[],[f307,f146])).

fof(f307,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
      | r1_tsep_1(X1,sK6)
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f298,f141])).

fof(f298,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6))
      | r1_tsep_1(X1,sK6)
      | ~ l1_struct_0(sK6)
      | ~ l1_struct_0(X1) ) ),
    inference(superposition,[],[f76,f144])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f73,f129,f125])).

fof(f73,plain,
    ( r1_tsep_1(sK8,sK7)
    | r1_tsep_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f43])).

fof(f123,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f72,f120,f116])).

fof(f72,plain,
    ( ~ r1_tsep_1(sK8,sK6)
    | ~ r1_tsep_1(sK6,sK8) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:15:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (4196)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.44  % (4182)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.45  % (4188)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (4177)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (4176)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (4173)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (4175)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (4181)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (4173)Refutation not found, incomplete strategy% (4173)------------------------------
% 0.20/0.50  % (4173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4189)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (4173)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4173)Memory used [KB]: 10618
% 0.20/0.51  % (4173)Time elapsed: 0.095 s
% 0.20/0.51  % (4173)------------------------------
% 0.20/0.51  % (4173)------------------------------
% 0.20/0.51  % (4185)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (4186)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (4191)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (4192)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (4186)Refutation not found, incomplete strategy% (4186)------------------------------
% 0.20/0.51  % (4186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4186)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4186)Memory used [KB]: 6268
% 0.20/0.51  % (4186)Time elapsed: 0.109 s
% 0.20/0.51  % (4186)------------------------------
% 0.20/0.51  % (4186)------------------------------
% 0.20/0.51  % (4178)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (4195)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (4179)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (4174)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (4193)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (4198)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (4190)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (4184)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (4194)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (4187)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (4197)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (4180)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.56/0.55  % (4183)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.71/0.61  % (4182)Refutation not found, incomplete strategy% (4182)------------------------------
% 1.71/0.61  % (4182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (4182)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (4182)Memory used [KB]: 6140
% 1.71/0.61  % (4182)Time elapsed: 0.175 s
% 1.71/0.61  % (4182)------------------------------
% 1.71/0.61  % (4182)------------------------------
% 4.06/0.92  % (4187)Time limit reached!
% 4.06/0.92  % (4187)------------------------------
% 4.06/0.92  % (4187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.92  % (4187)Termination reason: Time limit
% 4.06/0.92  
% 4.06/0.92  % (4187)Memory used [KB]: 7291
% 4.06/0.92  % (4187)Time elapsed: 0.517 s
% 4.06/0.92  % (4187)------------------------------
% 4.06/0.92  % (4187)------------------------------
% 4.82/1.00  % (4198)Refutation found. Thanks to Tanya!
% 4.82/1.00  % SZS status Theorem for theBenchmark
% 4.82/1.01  % SZS output start Proof for theBenchmark
% 4.82/1.01  fof(f5397,plain,(
% 4.82/1.01    $false),
% 4.82/1.01    inference(avatar_sat_refutation,[],[f123,f132,f1593,f1598,f3309,f5102,f5106,f5383,f5396])).
% 4.82/1.01  % (4179)Time limit reached!
% 4.82/1.01  % (4179)------------------------------
% 4.82/1.01  % (4179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.01  fof(f5396,plain,(
% 4.82/1.01    spl11_3 | ~spl11_4),
% 4.82/1.01    inference(avatar_contradiction_clause,[],[f5395])).
% 4.82/1.01  fof(f5395,plain,(
% 4.82/1.01    $false | (spl11_3 | ~spl11_4)),
% 4.82/1.01    inference(subsumption_resolution,[],[f5394,f143])).
% 4.82/1.01  fof(f143,plain,(
% 4.82/1.01    l1_struct_0(sK8)),
% 4.82/1.01    inference(resolution,[],[f140,f77])).
% 4.82/1.01  fof(f77,plain,(
% 4.82/1.01    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f19])).
% 4.82/1.01  fof(f19,plain,(
% 4.82/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.82/1.01    inference(ennf_transformation,[],[f6])).
% 4.82/1.01  fof(f6,axiom,(
% 4.82/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 4.82/1.01  fof(f140,plain,(
% 4.82/1.01    l1_pre_topc(sK8)),
% 4.82/1.01    inference(subsumption_resolution,[],[f136,f64])).
% 4.82/1.01  fof(f64,plain,(
% 4.82/1.01    l1_pre_topc(sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f43,plain,(
% 4.82/1.01    ((((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 4.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f16,f42,f41,f40,f39])).
% 4.82/1.01  fof(f39,plain,(
% 4.82/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 4.82/1.01    introduced(choice_axiom,[])).
% 4.82/1.01  fof(f40,plain,(
% 4.82/1.01    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK5) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) & m1_pre_topc(sK6,sK5) & ~v2_struct_0(sK6))),
% 4.82/1.01    introduced(choice_axiom,[])).
% 4.82/1.01  fof(f41,plain,(
% 4.82/1.01    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,X2) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK5) & ~v2_struct_0(X2)) => (? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) & m1_pre_topc(sK7,sK5) & ~v2_struct_0(sK7))),
% 4.82/1.01    introduced(choice_axiom,[])).
% 4.82/1.01  fof(f42,plain,(
% 4.82/1.01    ? [X3] : ((r1_tsep_1(X3,sK7) | r1_tsep_1(sK7,X3)) & (~r1_tsep_1(X3,sK6) | ~r1_tsep_1(sK6,X3)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(X3,sK5) & ~v2_struct_0(X3)) => ((r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)) & (~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)) & m1_pre_topc(sK6,sK7) & m1_pre_topc(sK8,sK5) & ~v2_struct_0(sK8))),
% 4.82/1.01    introduced(choice_axiom,[])).
% 4.82/1.01  fof(f16,plain,(
% 4.82/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.82/1.01    inference(flattening,[],[f15])).
% 4.82/1.01  fof(f15,plain,(
% 4.82/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.82/1.01    inference(ennf_transformation,[],[f14])).
% 4.82/1.01  fof(f14,negated_conjecture,(
% 4.82/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.82/1.01    inference(negated_conjecture,[],[f13])).
% 4.82/1.01  fof(f13,conjecture,(
% 4.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 4.82/1.01  fof(f136,plain,(
% 4.82/1.01    l1_pre_topc(sK8) | ~l1_pre_topc(sK5)),
% 4.82/1.01    inference(resolution,[],[f93,f70])).
% 4.82/1.01  fof(f70,plain,(
% 4.82/1.01    m1_pre_topc(sK8,sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f93,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f21])).
% 4.82/1.01  fof(f21,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.82/1.01    inference(ennf_transformation,[],[f7])).
% 4.82/1.01  fof(f7,axiom,(
% 4.82/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 4.82/1.01  fof(f5394,plain,(
% 4.82/1.01    ~l1_struct_0(sK8) | (spl11_3 | ~spl11_4)),
% 4.82/1.01    inference(subsumption_resolution,[],[f5393,f142])).
% 4.82/1.01  fof(f142,plain,(
% 4.82/1.01    l1_struct_0(sK7)),
% 4.82/1.01    inference(resolution,[],[f139,f77])).
% 4.82/1.01  fof(f139,plain,(
% 4.82/1.01    l1_pre_topc(sK7)),
% 4.82/1.01    inference(subsumption_resolution,[],[f135,f64])).
% 4.82/1.01  fof(f135,plain,(
% 4.82/1.01    l1_pre_topc(sK7) | ~l1_pre_topc(sK5)),
% 4.82/1.01    inference(resolution,[],[f93,f68])).
% 4.82/1.01  fof(f68,plain,(
% 4.82/1.01    m1_pre_topc(sK7,sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f5393,plain,(
% 4.82/1.01    ~l1_struct_0(sK7) | ~l1_struct_0(sK8) | (spl11_3 | ~spl11_4)),
% 4.82/1.01    inference(subsumption_resolution,[],[f5392,f126])).
% 4.82/1.01  fof(f126,plain,(
% 4.82/1.01    ~r1_tsep_1(sK7,sK8) | spl11_3),
% 4.82/1.01    inference(avatar_component_clause,[],[f125])).
% 4.82/1.01  fof(f125,plain,(
% 4.82/1.01    spl11_3 <=> r1_tsep_1(sK7,sK8)),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 4.82/1.01  fof(f5392,plain,(
% 4.82/1.01    r1_tsep_1(sK7,sK8) | ~l1_struct_0(sK7) | ~l1_struct_0(sK8) | ~spl11_4),
% 4.82/1.01    inference(resolution,[],[f131,f98])).
% 4.82/1.01  fof(f98,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f27])).
% 4.82/1.01  fof(f27,plain,(
% 4.82/1.01    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 4.82/1.01    inference(flattening,[],[f26])).
% 4.82/1.01  fof(f26,plain,(
% 4.82/1.01    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 4.82/1.01    inference(ennf_transformation,[],[f11])).
% 4.82/1.01  fof(f11,axiom,(
% 4.82/1.01    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 4.82/1.01  fof(f131,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK7) | ~spl11_4),
% 4.82/1.01    inference(avatar_component_clause,[],[f129])).
% 4.82/1.01  fof(f129,plain,(
% 4.82/1.01    spl11_4 <=> r1_tsep_1(sK8,sK7)),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 4.82/1.01  fof(f5383,plain,(
% 4.82/1.01    ~spl11_3 | spl11_27 | ~spl11_121),
% 4.82/1.01    inference(avatar_contradiction_clause,[],[f5382])).
% 4.82/1.01  fof(f5382,plain,(
% 4.82/1.01    $false | (~spl11_3 | spl11_27 | ~spl11_121)),
% 4.82/1.01    inference(subsumption_resolution,[],[f5381,f381])).
% 4.82/1.01  fof(f381,plain,(
% 4.82/1.01    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | spl11_27),
% 4.82/1.01    inference(avatar_component_clause,[],[f380])).
% 4.82/1.01  fof(f380,plain,(
% 4.82/1.01    spl11_27 <=> r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6))),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 4.82/1.01  fof(f5381,plain,(
% 4.82/1.01    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | (~spl11_3 | ~spl11_121)),
% 4.82/1.01    inference(resolution,[],[f5153,f377])).
% 4.82/1.01  fof(f377,plain,(
% 4.82/1.01    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~spl11_3),
% 4.82/1.01    inference(subsumption_resolution,[],[f376,f142])).
% 4.82/1.01  fof(f376,plain,(
% 4.82/1.01    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~l1_struct_0(sK7) | ~spl11_3),
% 4.82/1.01    inference(subsumption_resolution,[],[f373,f169])).
% 4.82/1.01  fof(f169,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK7) | ~spl11_3),
% 4.82/1.01    inference(subsumption_resolution,[],[f168,f142])).
% 4.82/1.01  fof(f168,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK7) | ~spl11_3),
% 4.82/1.01    inference(subsumption_resolution,[],[f167,f143])).
% 4.82/1.01  fof(f167,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK8) | ~l1_struct_0(sK7) | ~spl11_3),
% 4.82/1.01    inference(resolution,[],[f98,f127])).
% 4.82/1.01  fof(f127,plain,(
% 4.82/1.01    r1_tsep_1(sK7,sK8) | ~spl11_3),
% 4.82/1.01    inference(avatar_component_clause,[],[f125])).
% 4.82/1.01  fof(f373,plain,(
% 4.82/1.01    r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK7)) | ~r1_tsep_1(sK8,sK7) | ~l1_struct_0(sK7)),
% 4.82/1.01    inference(superposition,[],[f194,f145])).
% 4.82/1.01  fof(f145,plain,(
% 4.82/1.01    k2_struct_0(sK7) = u1_struct_0(sK7)),
% 4.82/1.01    inference(resolution,[],[f142,f74])).
% 4.82/1.01  fof(f74,plain,(
% 4.82/1.01    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f17])).
% 4.82/1.01  fof(f17,plain,(
% 4.82/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 4.82/1.01    inference(ennf_transformation,[],[f4])).
% 4.82/1.01  fof(f4,axiom,(
% 4.82/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 4.82/1.01  fof(f194,plain,(
% 4.82/1.01    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | ~r1_tsep_1(sK8,X3) | ~l1_struct_0(X3)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f186,f143])).
% 4.82/1.01  fof(f186,plain,(
% 4.82/1.01    ( ! [X3] : (r1_xboole_0(k2_struct_0(sK8),u1_struct_0(X3)) | ~r1_tsep_1(sK8,X3) | ~l1_struct_0(X3) | ~l1_struct_0(sK8)) )),
% 4.82/1.01    inference(superposition,[],[f75,f146])).
% 4.82/1.01  fof(f146,plain,(
% 4.82/1.01    k2_struct_0(sK8) = u1_struct_0(sK8)),
% 4.82/1.01    inference(resolution,[],[f143,f74])).
% 4.82/1.01  fof(f75,plain,(
% 4.82/1.01    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f44])).
% 4.82/1.01  fof(f44,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.82/1.01    inference(nnf_transformation,[],[f18])).
% 4.82/1.01  fof(f18,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 4.82/1.01    inference(ennf_transformation,[],[f9])).
% 4.82/1.01  fof(f9,axiom,(
% 4.82/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 4.82/1.01  fof(f5153,plain,(
% 4.82/1.01    ( ! [X2] : (~r1_xboole_0(X2,k2_struct_0(sK7)) | r1_xboole_0(X2,k2_struct_0(sK6))) ) | ~spl11_121),
% 4.82/1.01    inference(backward_demodulation,[],[f1968,f3503])).
% 4.82/1.01  fof(f3503,plain,(
% 4.82/1.01    k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) | ~spl11_121),
% 4.82/1.01    inference(avatar_component_clause,[],[f3501])).
% 4.82/1.01  fof(f3501,plain,(
% 4.82/1.01    spl11_121 <=> k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).
% 4.82/1.01  fof(f1968,plain,(
% 4.82/1.01    ( ! [X2] : (~r1_xboole_0(X2,k2_struct_0(k1_tsep_1(sK5,sK7,sK6))) | r1_xboole_0(X2,k2_struct_0(sK6))) )),
% 4.82/1.01    inference(superposition,[],[f104,f1939])).
% 4.82/1.01  fof(f1939,plain,(
% 4.82/1.01    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 4.82/1.01    inference(forward_demodulation,[],[f1938,f1127])).
% 4.82/1.01  fof(f1127,plain,(
% 4.82/1.01    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.82/1.01    inference(subsumption_resolution,[],[f1123,f65])).
% 4.82/1.01  fof(f65,plain,(
% 4.82/1.01    ~v2_struct_0(sK6)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f1123,plain,(
% 4.82/1.01    v2_struct_0(sK6) | k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.82/1.01    inference(resolution,[],[f909,f66])).
% 4.82/1.01  fof(f66,plain,(
% 4.82/1.01    m1_pre_topc(sK6,sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f909,plain,(
% 4.82/1.01    ( ! [X9] : (~m1_pre_topc(X9,sK5) | v2_struct_0(X9) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f908,f62])).
% 4.82/1.01  fof(f62,plain,(
% 4.82/1.01    ~v2_struct_0(sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f908,plain,(
% 4.82/1.01    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f907,f64])).
% 4.82/1.01  fof(f907,plain,(
% 4.82/1.01    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f891,f67])).
% 4.82/1.01  % (4179)Termination reason: Time limit
% 4.82/1.01  fof(f67,plain,(
% 4.82/1.01    ~v2_struct_0(sK7)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  % (4179)Termination phase: Saturation
% 4.82/1.01  fof(f891,plain,(
% 4.82/1.01    ( ! [X9] : (v2_struct_0(X9) | ~m1_pre_topc(X9,sK5) | v2_struct_0(sK7) | ~l1_pre_topc(sK5) | v2_struct_0(sK5) | k2_struct_0(k1_tsep_1(sK5,sK7,X9)) = u1_struct_0(k1_tsep_1(sK5,sK7,X9))) )),
% 4.82/1.01    inference(resolution,[],[f776,f68])).
% 4.82/1.01  
% 4.82/1.01  % (4179)Memory used [KB]: 15095
% 4.82/1.01  fof(f776,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | v2_struct_0(X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 4.82/1.01    inference(duplicate_literal_removal,[],[f775])).
% 4.82/1.01  % (4179)Time elapsed: 0.606 s
% 4.82/1.01  % (4179)------------------------------
% 4.82/1.01  % (4179)------------------------------
% 4.82/1.01  fof(f775,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X1) | k2_struct_0(k1_tsep_1(X1,X2,X0)) = u1_struct_0(k1_tsep_1(X1,X2,X0))) )),
% 4.82/1.01    inference(resolution,[],[f109,f180])).
% 4.82/1.01  fof(f180,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~l1_pre_topc(X0) | k2_struct_0(k1_tsep_1(X0,X2,X1)) = u1_struct_0(k1_tsep_1(X0,X2,X1))) )),
% 4.82/1.01    inference(resolution,[],[f179,f74])).
% 4.82/1.01  fof(f179,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (l1_struct_0(k1_tsep_1(X0,X2,X1)) | ~l1_pre_topc(X0) | ~sP4(X0,X1,X2)) )),
% 4.82/1.01    inference(resolution,[],[f172,f77])).
% 4.82/1.01  fof(f172,plain,(
% 4.82/1.01    ( ! [X4,X5,X3] : (l1_pre_topc(k1_tsep_1(X3,X5,X4)) | ~sP4(X3,X4,X5) | ~l1_pre_topc(X3)) )),
% 4.82/1.01    inference(resolution,[],[f108,f93])).
% 4.82/1.01  fof(f108,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP4(X0,X1,X2)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f61])).
% 4.82/1.01  fof(f61,plain,(
% 4.82/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP4(X0,X1,X2))),
% 4.82/1.01    inference(rectify,[],[f60])).
% 4.82/1.01  fof(f60,plain,(
% 4.82/1.01    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 4.82/1.01    inference(nnf_transformation,[],[f37])).
% 4.82/1.01  fof(f37,plain,(
% 4.82/1.01    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP4(X0,X2,X1))),
% 4.82/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 4.82/1.01  fof(f109,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f38])).
% 4.82/1.01  fof(f38,plain,(
% 4.82/1.01    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.82/1.01    inference(definition_folding,[],[f31,f37])).
% 4.82/1.01  fof(f31,plain,(
% 4.82/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.82/1.01    inference(flattening,[],[f30])).
% 4.82/1.01  fof(f30,plain,(
% 4.82/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.82/1.01    inference(ennf_transformation,[],[f10])).
% 4.82/1.01  fof(f10,axiom,(
% 4.82/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 4.82/1.01  fof(f1938,plain,(
% 4.82/1.01    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6))),
% 4.82/1.01    inference(forward_demodulation,[],[f1937,f145])).
% 4.82/1.01  fof(f1937,plain,(
% 4.82/1.01    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6))),
% 4.82/1.01    inference(subsumption_resolution,[],[f1931,f67])).
% 4.82/1.01  fof(f1931,plain,(
% 4.82/1.01    u1_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) | v2_struct_0(sK7)),
% 4.82/1.01    inference(resolution,[],[f1900,f68])).
% 4.82/1.01  fof(f1900,plain,(
% 4.82/1.01    ( ! [X8] : (~m1_pre_topc(X8,sK5) | u1_struct_0(k1_tsep_1(sK5,X8,sK6)) = k2_xboole_0(u1_struct_0(X8),k2_struct_0(sK6)) | v2_struct_0(X8)) )),
% 4.82/1.01    inference(forward_demodulation,[],[f1899,f144])).
% 4.82/1.01  fof(f144,plain,(
% 4.82/1.01    k2_struct_0(sK6) = u1_struct_0(sK6)),
% 4.82/1.01    inference(resolution,[],[f141,f74])).
% 4.82/1.01  fof(f141,plain,(
% 4.82/1.01    l1_struct_0(sK6)),
% 4.82/1.01    inference(resolution,[],[f138,f77])).
% 4.82/1.01  fof(f138,plain,(
% 4.82/1.01    l1_pre_topc(sK6)),
% 4.82/1.01    inference(subsumption_resolution,[],[f134,f64])).
% 4.82/1.01  fof(f134,plain,(
% 4.82/1.01    l1_pre_topc(sK6) | ~l1_pre_topc(sK5)),
% 4.82/1.01    inference(resolution,[],[f93,f66])).
% 4.82/1.01  fof(f1899,plain,(
% 4.82/1.01    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1898,f62])).
% 4.82/1.01  fof(f1898,plain,(
% 4.82/1.01    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | v2_struct_0(sK5)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1897,f64])).
% 4.82/1.01  fof(f1897,plain,(
% 4.82/1.01    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1881,f65])).
% 4.82/1.01  fof(f1881,plain,(
% 4.82/1.01    ( ! [X8] : (k2_xboole_0(u1_struct_0(X8),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK5,X8,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X8,sK5) | v2_struct_0(X8) | ~l1_pre_topc(sK5) | v2_struct_0(sK5)) )),
% 4.82/1.01    inference(resolution,[],[f1579,f66])).
% 4.82/1.01  fof(f1579,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1578,f109])).
% 4.82/1.01  fof(f1578,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1577,f106])).
% 4.82/1.01  fof(f106,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f61])).
% 4.82/1.01  fof(f1577,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1576,f107])).
% 4.82/1.01  fof(f107,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP4(X0,X1,X2)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f61])).
% 4.82/1.01  fof(f1576,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(X2,X0,X1)) | ~v1_pre_topc(k1_tsep_1(X2,X0,X1)) | v2_struct_0(k1_tsep_1(X2,X0,X1)) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~sP4(X2,X1,X0)) )),
% 4.82/1.01    inference(resolution,[],[f111,f108])).
% 4.82/1.01  fof(f111,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.82/1.01    inference(equality_resolution,[],[f94])).
% 4.82/1.01  fof(f94,plain,(
% 4.82/1.01    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f56])).
% 4.82/1.01  fof(f56,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.82/1.01    inference(nnf_transformation,[],[f23])).
% 4.82/1.01  fof(f23,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.82/1.01    inference(flattening,[],[f22])).
% 4.82/1.01  fof(f22,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.82/1.01    inference(ennf_transformation,[],[f8])).
% 4.82/1.01  fof(f8,axiom,(
% 4.82/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 4.82/1.01  fof(f104,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f28])).
% 4.82/1.01  fof(f28,plain,(
% 4.82/1.01    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.82/1.01    inference(ennf_transformation,[],[f3])).
% 4.82/1.01  fof(f3,axiom,(
% 4.82/1.01    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 4.82/1.01  fof(f5106,plain,(
% 4.82/1.01    spl11_74 | ~spl11_99),
% 4.82/1.01    inference(avatar_contradiction_clause,[],[f5105])).
% 4.82/1.01  fof(f5105,plain,(
% 4.82/1.01    $false | (spl11_74 | ~spl11_99)),
% 4.82/1.01    inference(subsumption_resolution,[],[f5103,f3333])).
% 4.82/1.01  fof(f3333,plain,(
% 4.82/1.01    sP2(k1_tsep_1(sK7,sK7,sK6),sK7) | ~spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3316,f139])).
% 4.82/1.01  fof(f3316,plain,(
% 4.82/1.01    sP2(k1_tsep_1(sK7,sK7,sK6),sK7) | ~l1_pre_topc(sK7) | ~spl11_99),
% 4.82/1.01    inference(resolution,[],[f3298,f151])).
% 4.82/1.01  fof(f151,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X1)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f150,f93])).
% 4.82/1.01  fof(f150,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | sP2(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 4.82/1.01    inference(resolution,[],[f78,f92])).
% 4.82/1.01  fof(f92,plain,(
% 4.82/1.01    ( ! [X0,X1] : (sP3(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f36])).
% 4.82/1.01  fof(f36,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (sP3(X0,X1) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.82/1.01    inference(definition_folding,[],[f20,f35,f34,f33,f32])).
% 4.82/1.01  fof(f32,plain,(
% 4.82/1.01    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.82/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.82/1.01  fof(f33,plain,(
% 4.82/1.01    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> sP0(X2,X1,X0)))),
% 4.82/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.82/1.01  fof(f34,plain,(
% 4.82/1.01    ! [X1,X0] : (sP2(X1,X0) <=> (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))),
% 4.82/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 4.82/1.01  fof(f35,plain,(
% 4.82/1.01    ! [X0,X1] : ((m1_pre_topc(X1,X0) <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 4.82/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 4.82/1.01  fof(f20,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.82/1.01    inference(ennf_transformation,[],[f5])).
% 4.82/1.01  fof(f5,axiom,(
% 4.82/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 4.82/1.01  fof(f78,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~sP3(X0,X1) | ~m1_pre_topc(X1,X0) | sP2(X1,X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f45])).
% 4.82/1.01  fof(f45,plain,(
% 4.82/1.01    ! [X0,X1] : (((m1_pre_topc(X1,X0) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~m1_pre_topc(X1,X0))) | ~sP3(X0,X1))),
% 4.82/1.01    inference(nnf_transformation,[],[f35])).
% 4.82/1.01  fof(f3298,plain,(
% 4.82/1.01    m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) | ~spl11_99),
% 4.82/1.01    inference(avatar_component_clause,[],[f3297])).
% 4.82/1.01  fof(f3297,plain,(
% 4.82/1.01    spl11_99 <=> m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7)),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).
% 4.82/1.01  fof(f5103,plain,(
% 4.82/1.01    ~sP2(k1_tsep_1(sK7,sK7,sK6),sK7) | (spl11_74 | ~spl11_99)),
% 4.82/1.01    inference(resolution,[],[f1817,f3364])).
% 4.82/1.01  fof(f3364,plain,(
% 4.82/1.01    ( ! [X0] : (r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(X0)) | ~sP2(k1_tsep_1(sK7,sK7,sK6),X0)) ) | ~spl11_99),
% 4.82/1.01    inference(superposition,[],[f80,f3337])).
% 4.82/1.01  fof(f3337,plain,(
% 4.82/1.01    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~spl11_99),
% 4.82/1.01    inference(forward_demodulation,[],[f3336,f2824])).
% 4.82/1.01  fof(f2824,plain,(
% 4.82/1.01    k2_struct_0(k1_tsep_1(sK5,sK7,sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.82/1.01    inference(forward_demodulation,[],[f2823,f1939])).
% 4.82/1.01  fof(f2823,plain,(
% 4.82/1.01    k2_xboole_0(k2_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.82/1.01    inference(backward_demodulation,[],[f2639,f145])).
% 4.82/1.01  fof(f2639,plain,(
% 4.82/1.01    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6))),
% 4.82/1.01    inference(subsumption_resolution,[],[f2633,f67])).
% 4.82/1.01  fof(f2633,plain,(
% 4.82/1.01    k2_xboole_0(u1_struct_0(sK7),k2_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) | v2_struct_0(sK7)),
% 4.82/1.01    inference(resolution,[],[f1915,f560])).
% 4.82/1.01  fof(f560,plain,(
% 4.82/1.01    m1_pre_topc(sK7,sK7)),
% 4.82/1.01    inference(subsumption_resolution,[],[f559,f63])).
% 4.82/1.01  fof(f63,plain,(
% 4.82/1.01    v2_pre_topc(sK5)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f559,plain,(
% 4.82/1.01    m1_pre_topc(sK7,sK7) | ~v2_pre_topc(sK5)),
% 4.82/1.01    inference(subsumption_resolution,[],[f553,f64])).
% 4.82/1.01  fof(f553,plain,(
% 4.82/1.01    m1_pre_topc(sK7,sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 4.82/1.01    inference(resolution,[],[f551,f68])).
% 4.82/1.01  fof(f551,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 4.82/1.01    inference(duplicate_literal_removal,[],[f542])).
% 4.82/1.01  fof(f542,plain,(
% 4.82/1.01    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 4.82/1.01    inference(resolution,[],[f96,f112])).
% 4.82/1.01  fof(f112,plain,(
% 4.82/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.82/1.01    inference(equality_resolution,[],[f100])).
% 4.82/1.01  fof(f100,plain,(
% 4.82/1.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.82/1.01    inference(cnf_transformation,[],[f59])).
% 4.82/1.01  fof(f59,plain,(
% 4.82/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.82/1.01    inference(flattening,[],[f58])).
% 4.82/1.01  fof(f58,plain,(
% 4.82/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.82/1.01    inference(nnf_transformation,[],[f1])).
% 4.82/1.01  fof(f1,axiom,(
% 4.82/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.82/1.01  fof(f96,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f57])).
% 4.82/1.01  fof(f57,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.82/1.01    inference(nnf_transformation,[],[f25])).
% 4.82/1.01  fof(f25,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.82/1.01    inference(flattening,[],[f24])).
% 4.82/1.01  fof(f24,plain,(
% 4.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.82/1.01    inference(ennf_transformation,[],[f12])).
% 4.82/1.01  fof(f12,axiom,(
% 4.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 4.82/1.01  fof(f1915,plain,(
% 4.82/1.01    ( ! [X12] : (~m1_pre_topc(X12,sK7) | u1_struct_0(k1_tsep_1(sK7,X12,sK6)) = k2_xboole_0(u1_struct_0(X12),k2_struct_0(sK6)) | v2_struct_0(X12)) )),
% 4.82/1.01    inference(forward_demodulation,[],[f1914,f144])).
% 4.82/1.01  fof(f1914,plain,(
% 4.82/1.01    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1913,f67])).
% 4.82/1.01  fof(f1913,plain,(
% 4.82/1.01    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | v2_struct_0(sK7)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1912,f139])).
% 4.82/1.01  fof(f1912,plain,(
% 4.82/1.01    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f1885,f65])).
% 4.82/1.01  fof(f1885,plain,(
% 4.82/1.01    ( ! [X12] : (k2_xboole_0(u1_struct_0(X12),u1_struct_0(sK6)) = u1_struct_0(k1_tsep_1(sK7,X12,sK6)) | v2_struct_0(sK6) | ~m1_pre_topc(X12,sK7) | v2_struct_0(X12) | ~l1_pre_topc(sK7) | v2_struct_0(sK7)) )),
% 4.82/1.01    inference(resolution,[],[f1579,f71])).
% 4.82/1.01  fof(f71,plain,(
% 4.82/1.01    m1_pre_topc(sK6,sK7)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f3336,plain,(
% 4.82/1.01    u1_struct_0(k1_tsep_1(sK7,sK7,sK6)) = k2_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~spl11_99),
% 4.82/1.01    inference(resolution,[],[f3335,f74])).
% 4.82/1.01  fof(f3335,plain,(
% 4.82/1.01    l1_struct_0(k1_tsep_1(sK7,sK7,sK6)) | ~spl11_99),
% 4.82/1.01    inference(resolution,[],[f3334,f77])).
% 4.82/1.01  fof(f3334,plain,(
% 4.82/1.01    l1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) | ~spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3317,f139])).
% 4.82/1.01  fof(f3317,plain,(
% 4.82/1.01    l1_pre_topc(k1_tsep_1(sK7,sK7,sK6)) | ~l1_pre_topc(sK7) | ~spl11_99),
% 4.82/1.01    inference(resolution,[],[f3298,f93])).
% 4.82/1.01  fof(f80,plain,(
% 4.82/1.01    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) | ~sP2(X0,X1)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f50])).
% 4.82/1.01  fof(f50,plain,(
% 4.82/1.01    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 4.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f48,f49])).
% 4.82/1.01  fof(f49,plain,(
% 4.82/1.01    ! [X1,X0] : (? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(X1,X0,sK9(X0,X1)) & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.82/1.01    introduced(choice_axiom,[])).
% 4.82/1.01  fof(f48,plain,(
% 4.82/1.01    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) & ((! [X3] : (sP1(X1,X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(k2_struct_0(X0),k2_struct_0(X1))) | ~sP2(X0,X1)))),
% 4.82/1.01    inference(rectify,[],[f47])).
% 4.82/1.01  fof(f47,plain,(
% 4.82/1.01    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 4.82/1.01    inference(flattening,[],[f46])).
% 4.82/1.01  fof(f46,plain,(
% 4.82/1.01    ! [X1,X0] : ((sP2(X1,X0) | (? [X2] : (~sP1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~sP2(X1,X0)))),
% 4.82/1.01    inference(nnf_transformation,[],[f34])).
% 4.82/1.01  fof(f1817,plain,(
% 4.82/1.01    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | spl11_74),
% 4.82/1.01    inference(avatar_component_clause,[],[f1816])).
% 4.82/1.01  fof(f1816,plain,(
% 4.82/1.01    spl11_74 <=> r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7))),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).
% 4.82/1.01  fof(f5102,plain,(
% 4.82/1.01    spl11_121 | ~spl11_74),
% 4.82/1.01    inference(avatar_split_clause,[],[f1973,f1816,f3501])).
% 4.82/1.01  fof(f1973,plain,(
% 4.82/1.01    ~r1_tarski(k2_struct_0(k1_tsep_1(sK5,sK7,sK6)),k2_struct_0(sK7)) | k2_struct_0(sK7) = k2_struct_0(k1_tsep_1(sK5,sK7,sK6))),
% 4.82/1.01    inference(superposition,[],[f162,f1939])).
% 4.82/1.01  fof(f162,plain,(
% 4.82/1.01    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 4.82/1.01    inference(resolution,[],[f101,f147])).
% 4.82/1.01  fof(f147,plain,(
% 4.82/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.82/1.01    inference(resolution,[],[f105,f112])).
% 4.82/1.01  fof(f105,plain,(
% 4.82/1.01    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f29])).
% 4.82/1.01  fof(f29,plain,(
% 4.82/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.82/1.01    inference(ennf_transformation,[],[f2])).
% 4.82/1.01  fof(f2,axiom,(
% 4.82/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.82/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 4.82/1.01  fof(f101,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f59])).
% 4.82/1.01  fof(f3309,plain,(
% 4.82/1.01    spl11_99),
% 4.82/1.01    inference(avatar_contradiction_clause,[],[f3308])).
% 4.82/1.01  fof(f3308,plain,(
% 4.82/1.01    $false | spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3307,f139])).
% 4.82/1.01  fof(f3307,plain,(
% 4.82/1.01    ~l1_pre_topc(sK7) | spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3306,f67])).
% 4.82/1.01  fof(f3306,plain,(
% 4.82/1.01    v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3305,f560])).
% 4.82/1.01  fof(f3305,plain,(
% 4.82/1.01    ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3304,f65])).
% 4.82/1.01  fof(f3304,plain,(
% 4.82/1.01    v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_99),
% 4.82/1.01    inference(subsumption_resolution,[],[f3303,f71])).
% 4.82/1.01  fof(f3303,plain,(
% 4.82/1.01    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | spl11_99),
% 4.82/1.01    inference(duplicate_literal_removal,[],[f3302])).
% 4.82/1.01  fof(f3302,plain,(
% 4.82/1.01    ~m1_pre_topc(sK6,sK7) | v2_struct_0(sK6) | ~m1_pre_topc(sK7,sK7) | v2_struct_0(sK7) | ~l1_pre_topc(sK7) | v2_struct_0(sK7) | spl11_99),
% 4.82/1.01    inference(resolution,[],[f3301,f109])).
% 4.82/1.01  fof(f3301,plain,(
% 4.82/1.01    ~sP4(sK7,sK6,sK7) | spl11_99),
% 4.82/1.01    inference(resolution,[],[f3299,f108])).
% 4.82/1.01  fof(f3299,plain,(
% 4.82/1.01    ~m1_pre_topc(k1_tsep_1(sK7,sK7,sK6),sK7) | spl11_99),
% 4.82/1.01    inference(avatar_component_clause,[],[f3297])).
% 4.82/1.01  fof(f1598,plain,(
% 4.82/1.01    spl11_1 | ~spl11_2),
% 4.82/1.01    inference(avatar_contradiction_clause,[],[f1597])).
% 4.82/1.01  fof(f1597,plain,(
% 4.82/1.01    $false | (spl11_1 | ~spl11_2)),
% 4.82/1.01    inference(subsumption_resolution,[],[f1596,f143])).
% 4.82/1.01  fof(f1596,plain,(
% 4.82/1.01    ~l1_struct_0(sK8) | (spl11_1 | ~spl11_2)),
% 4.82/1.01    inference(subsumption_resolution,[],[f1595,f141])).
% 4.82/1.01  fof(f1595,plain,(
% 4.82/1.01    ~l1_struct_0(sK6) | ~l1_struct_0(sK8) | (spl11_1 | ~spl11_2)),
% 4.82/1.01    inference(subsumption_resolution,[],[f1594,f118])).
% 4.82/1.01  fof(f118,plain,(
% 4.82/1.01    ~r1_tsep_1(sK6,sK8) | spl11_1),
% 4.82/1.01    inference(avatar_component_clause,[],[f116])).
% 4.82/1.01  fof(f116,plain,(
% 4.82/1.01    spl11_1 <=> r1_tsep_1(sK6,sK8)),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 4.82/1.01  fof(f1594,plain,(
% 4.82/1.01    r1_tsep_1(sK6,sK8) | ~l1_struct_0(sK6) | ~l1_struct_0(sK8) | ~spl11_2),
% 4.82/1.01    inference(resolution,[],[f121,f98])).
% 4.82/1.01  fof(f121,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK6) | ~spl11_2),
% 4.82/1.01    inference(avatar_component_clause,[],[f120])).
% 4.82/1.01  fof(f120,plain,(
% 4.82/1.01    spl11_2 <=> r1_tsep_1(sK8,sK6)),
% 4.82/1.01    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 4.82/1.01  fof(f1593,plain,(
% 4.82/1.01    spl11_2 | ~spl11_27),
% 4.82/1.01    inference(avatar_split_clause,[],[f1375,f380,f120])).
% 4.82/1.01  fof(f1375,plain,(
% 4.82/1.01    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_tsep_1(sK8,sK6)),
% 4.82/1.01    inference(subsumption_resolution,[],[f445,f143])).
% 4.82/1.01  fof(f445,plain,(
% 4.82/1.01    ~r1_xboole_0(k2_struct_0(sK8),k2_struct_0(sK6)) | r1_tsep_1(sK8,sK6) | ~l1_struct_0(sK8)),
% 4.82/1.01    inference(superposition,[],[f307,f146])).
% 4.82/1.01  fof(f307,plain,(
% 4.82/1.01    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | r1_tsep_1(X1,sK6) | ~l1_struct_0(X1)) )),
% 4.82/1.01    inference(subsumption_resolution,[],[f298,f141])).
% 4.82/1.01  fof(f298,plain,(
% 4.82/1.01    ( ! [X1] : (~r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK6)) | r1_tsep_1(X1,sK6) | ~l1_struct_0(sK6) | ~l1_struct_0(X1)) )),
% 4.82/1.01    inference(superposition,[],[f76,f144])).
% 4.82/1.01  fof(f76,plain,(
% 4.82/1.01    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 4.82/1.01    inference(cnf_transformation,[],[f44])).
% 4.82/1.01  fof(f132,plain,(
% 4.82/1.01    spl11_3 | spl11_4),
% 4.82/1.01    inference(avatar_split_clause,[],[f73,f129,f125])).
% 4.82/1.01  fof(f73,plain,(
% 4.82/1.01    r1_tsep_1(sK8,sK7) | r1_tsep_1(sK7,sK8)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  fof(f123,plain,(
% 4.82/1.01    ~spl11_1 | ~spl11_2),
% 4.82/1.01    inference(avatar_split_clause,[],[f72,f120,f116])).
% 4.82/1.01  fof(f72,plain,(
% 4.82/1.01    ~r1_tsep_1(sK8,sK6) | ~r1_tsep_1(sK6,sK8)),
% 4.82/1.01    inference(cnf_transformation,[],[f43])).
% 4.82/1.01  % SZS output end Proof for theBenchmark
% 4.82/1.01  % (4198)------------------------------
% 4.82/1.01  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.01  % (4198)Termination reason: Refutation
% 4.82/1.01  
% 4.82/1.01  % (4198)Memory used [KB]: 15607
% 4.82/1.01  % (4198)Time elapsed: 0.591 s
% 4.82/1.01  % (4198)------------------------------
% 4.82/1.01  % (4198)------------------------------
% 4.82/1.02  % (4172)Success in time 0.666 s
%------------------------------------------------------------------------------

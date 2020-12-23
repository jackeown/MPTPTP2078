%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 400 expanded)
%              Number of leaves         :   16 ( 169 expanded)
%              Depth                    :   12
%              Number of atoms          :  296 (4191 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f65,f85,f100,f101,f102])).

fof(f102,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f62,f58])).

fof(f58,plain,
    ( spl4_3
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f62,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f89,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f77,f76,f64,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f64,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f76,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f70,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f72,f41])).

fof(f72,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f29,f35,f42])).

fof(f35,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f87,f53,f49])).

fof(f49,plain,
    ( spl4_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f73,f77,f55,f44])).

fof(f55,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f68,f41])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f29,f31,f42])).

fof(f31,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f98,f94])).

fof(f94,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f36,f70,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f36,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl4_1
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f83,f84,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f84,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f73,f51,f77,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f51,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f83,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f76,f60,f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f58,f62])).

fof(f82,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f76,f60,f77,f44])).

fof(f65,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f37,f62,f58])).

fof(f37,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f38,f53,f49])).

fof(f38,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (8760)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.43  % (8760)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f56,f65,f85,f100,f101,f102])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl4_3 | ~spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f89,f62,f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl4_3 <=> r1_tsep_1(sK2,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl4_4 <=> r1_tsep_1(sK3,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    r1_tsep_1(sK2,sK3) | ~spl4_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f77,f76,f64,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    r1_tsep_1(sK3,sK2) | ~spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    l1_struct_0(sK2)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f70,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    l1_pre_topc(sK2)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f29,f33,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    m1_pre_topc(sK2,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ((((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    l1_struct_0(sK3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f72,f41])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    l1_pre_topc(sK3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f29,f35,f42])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m1_pre_topc(sK3,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~spl4_1 | spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f87,f53,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl4_1 <=> r1_tsep_1(sK1,sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl4_2 <=> r1_tsep_1(sK3,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    ~r1_tsep_1(sK1,sK3) | spl4_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f73,f77,f55,f44])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ~r1_tsep_1(sK3,sK1) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    l1_struct_0(sK1)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f68,f41])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    l1_pre_topc(sK1)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f29,f31,f42])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl4_1 | ~spl4_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    $false | (spl4_1 | ~spl4_3)),
% 0.21/0.44    inference(subsumption_resolution,[],[f98,f94])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f74,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.44    inference(nnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f36,f70,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    m1_pre_topc(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl4_1 | ~spl4_3)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f83,f84,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ~r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | spl4_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f73,f51,f77,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ~r1_tsep_1(sK1,sK3) | spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl4_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f76,f60,f77,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    r1_tsep_1(sK2,sK3) | ~spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f58])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl4_4 | ~spl4_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f82,f58,f62])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    r1_tsep_1(sK3,sK2) | ~spl4_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f76,f60,f77,f44])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl4_3 | spl4_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f62,f58])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~spl4_1 | ~spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f53,f49])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (8760)------------------------------
% 0.21/0.44  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (8760)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (8760)Memory used [KB]: 9850
% 0.21/0.44  % (8760)Time elapsed: 0.032 s
% 0.21/0.44  % (8760)------------------------------
% 0.21/0.44  % (8760)------------------------------
% 0.21/0.44  % (8742)Success in time 0.081 s
%------------------------------------------------------------------------------

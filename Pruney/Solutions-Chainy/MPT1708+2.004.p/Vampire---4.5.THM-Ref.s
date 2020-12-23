%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 686 expanded)
%              Number of leaves         :   21 ( 245 expanded)
%              Depth                    :   23
%              Number of atoms          :  724 (7347 expanded)
%              Number of equality atoms :   72 (1275 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4037,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f103,f238,f330,f338,f1695,f4023,f4036])).

fof(f4036,plain,
    ( ~ spl5_3
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f4035])).

fof(f4035,plain,
    ( $false
    | ~ spl5_3
    | spl5_20 ),
    inference(subsumption_resolution,[],[f4034,f255])).

fof(f255,plain,(
    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f218,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      | ! [X5] :
          ( sK3 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
    & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
          & ~ r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2))) )
        & ~ r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) )
   => ( ( ! [X4] :
            ( sK3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        | ! [X5] :
            ( sK3 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )
      & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
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
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,negated_conjecture,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f218,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f116,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f116,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X0] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,(
    ! [X0] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X0] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f41,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f4034,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_3
    | spl5_20 ),
    inference(resolution,[],[f4031,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4031,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_3
    | spl5_20 ),
    inference(subsumption_resolution,[],[f4028,f228])).

fof(f228,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_20
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f4028,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f98,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f98,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_3
  <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f4023,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f4022])).

fof(f4022,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f4021,f92])).

fof(f92,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f88,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f46])).

fof(f4021,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f4020,f45])).

fof(f4020,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f4018,f40])).

fof(f4018,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f3948,f47])).

fof(f3948,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | spl5_2
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f3947,f79])).

fof(f79,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3947,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f3946,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3946,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f3945,f1618])).

fof(f1618,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f812,f102])).

fof(f102,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_4
  <=> r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f812,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
        | r2_hidden(X2,u1_struct_0(sK1)) )
    | ~ spl5_22 ),
    inference(superposition,[],[f71,f237])).

fof(f237,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl5_22
  <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f3945,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f3944,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3944,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f813,f102])).

fof(f813,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
        | ~ r2_hidden(X3,k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) )
    | ~ spl5_22 ),
    inference(superposition,[],[f70,f237])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1695,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f1694])).

fof(f1694,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1693,f86])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f46])).

fof(f1693,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f1623,f45])).

fof(f1623,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1621,f38])).

fof(f1621,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f1620,f47])).

fof(f1620,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1619,f75])).

fof(f75,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_1
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1619,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(resolution,[],[f1618,f52])).

fof(f338,plain,(
    spl5_21 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl5_21 ),
    inference(subsumption_resolution,[],[f336,f36])).

fof(f336,plain,
    ( v2_struct_0(sK0)
    | spl5_21 ),
    inference(subsumption_resolution,[],[f335,f37])).

fof(f335,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_21 ),
    inference(subsumption_resolution,[],[f334,f38])).

fof(f334,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_21 ),
    inference(subsumption_resolution,[],[f333,f39])).

fof(f333,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_21 ),
    inference(subsumption_resolution,[],[f332,f40])).

fof(f332,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_21 ),
    inference(subsumption_resolution,[],[f331,f41])).

fof(f331,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_21 ),
    inference(resolution,[],[f233,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl5_21
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f330,plain,(
    ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f328,f36])).

fof(f328,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f327,f37])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f326,f38])).

fof(f326,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f325,f39])).

fof(f325,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f324,f40])).

fof(f324,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f323,f41])).

fof(f323,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_20 ),
    inference(resolution,[],[f229,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f229,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f238,plain,
    ( spl5_20
    | ~ spl5_21
    | spl5_22 ),
    inference(avatar_split_clause,[],[f225,f235,f231,f227])).

fof(f225,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f224,f36])).

fof(f224,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f37])).

fof(f223,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f38])).

fof(f222,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f39])).

fof(f221,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f40])).

fof(f220,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f219,f41])).

fof(f219,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f42])).

fof(f42,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f214,plain,
    ( u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f116,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))
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
    inference(definition_unfolding,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f103,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f93,f100,f96])).

fof(f93,plain,
    ( r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f77,f73])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X5] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (13256)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (13244)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (13261)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (13251)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (13245)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13254)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (13264)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (13255)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13270)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (13243)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (13271)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (13246)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (13265)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (13266)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13257)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13262)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (13260)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (13258)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13248)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (13247)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (13267)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (13265)Refutation not found, incomplete strategy% (13265)------------------------------
% 0.21/0.53  % (13265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13265)Memory used [KB]: 10746
% 0.21/0.53  % (13265)Time elapsed: 0.090 s
% 0.21/0.53  % (13265)------------------------------
% 0.21/0.53  % (13265)------------------------------
% 0.21/0.54  % (13269)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (13249)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13259)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (13252)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (13253)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (13272)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (13253)Refutation not found, incomplete strategy% (13253)------------------------------
% 0.21/0.55  % (13253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13253)Memory used [KB]: 10746
% 0.21/0.55  % (13253)Time elapsed: 0.150 s
% 0.21/0.55  % (13253)------------------------------
% 0.21/0.55  % (13253)------------------------------
% 0.21/0.55  % (13268)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13263)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.83/0.60  % (13251)Refutation found. Thanks to Tanya!
% 1.83/0.60  % SZS status Theorem for theBenchmark
% 1.83/0.62  % SZS output start Proof for theBenchmark
% 1.83/0.62  fof(f4037,plain,(
% 1.83/0.62    $false),
% 1.83/0.62    inference(avatar_sat_refutation,[],[f80,f103,f238,f330,f338,f1695,f4023,f4036])).
% 1.83/0.62  fof(f4036,plain,(
% 1.83/0.62    ~spl5_3 | spl5_20),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f4035])).
% 1.83/0.62  fof(f4035,plain,(
% 1.83/0.62    $false | (~spl5_3 | spl5_20)),
% 1.83/0.62    inference(subsumption_resolution,[],[f4034,f255])).
% 1.83/0.62  fof(f255,plain,(
% 1.83/0.62    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.83/0.62    inference(subsumption_resolution,[],[f218,f37])).
% 1.83/0.62  fof(f37,plain,(
% 1.83/0.62    l1_pre_topc(sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f28,plain,(
% 1.83/0.62    ((((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.83/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f27,f26,f25,f24])).
% 1.83/0.62  fof(f24,plain,(
% 1.83/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f25,plain,(
% 1.83/0.62    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f26,plain,(
% 1.83/0.62    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,X2)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f27,plain,(
% 1.83/0.62    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))) => ((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) | ! [X5] : (sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1)))) & m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f14,plain,(
% 1.83/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.83/0.62    inference(flattening,[],[f13])).
% 1.83/0.62  fof(f13,plain,(
% 1.83/0.62    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f12])).
% 1.83/0.62  fof(f12,plain,(
% 1.83/0.62    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.83/0.62    inference(pure_predicate_removal,[],[f11])).
% 1.83/0.62  fof(f11,plain,(
% 1.83/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 1.83/0.62    inference(rectify,[],[f10])).
% 1.83/0.62  fof(f10,negated_conjecture,(
% 1.83/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.83/0.62    inference(negated_conjecture,[],[f9])).
% 1.83/0.62  fof(f9,conjecture,(
% 1.83/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).
% 1.83/0.62  fof(f218,plain,(
% 1.83/0.62    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0)),
% 1.83/0.62    inference(resolution,[],[f116,f46])).
% 1.83/0.62  fof(f46,plain,(
% 1.83/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f16])).
% 1.83/0.62  fof(f16,plain,(
% 1.83/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.83/0.62    inference(ennf_transformation,[],[f5])).
% 1.83/0.62  fof(f5,axiom,(
% 1.83/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.83/0.62  fof(f116,plain,(
% 1.83/0.62    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f114,f38])).
% 1.83/0.62  fof(f38,plain,(
% 1.83/0.62    ~v2_struct_0(sK1)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f114,plain,(
% 1.83/0.62    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK1)),
% 1.83/0.62    inference(resolution,[],[f91,f39])).
% 1.83/0.62  fof(f39,plain,(
% 1.83/0.62    m1_pre_topc(sK1,sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f91,plain,(
% 1.83/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(subsumption_resolution,[],[f90,f36])).
% 1.83/0.62  fof(f36,plain,(
% 1.83/0.62    ~v2_struct_0(sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f90,plain,(
% 1.83/0.62    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 1.83/0.62    inference(subsumption_resolution,[],[f89,f37])).
% 1.83/0.62  fof(f89,plain,(
% 1.83/0.62    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.83/0.62    inference(subsumption_resolution,[],[f87,f40])).
% 1.83/0.62  fof(f40,plain,(
% 1.83/0.62    ~v2_struct_0(sK2)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f87,plain,(
% 1.83/0.62    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.83/0.62    inference(resolution,[],[f41,f57])).
% 1.83/0.62  fof(f57,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f23])).
% 1.83/0.62  fof(f23,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.62    inference(flattening,[],[f22])).
% 1.83/0.62  fof(f22,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f8])).
% 1.83/0.62  fof(f8,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.83/0.62  fof(f41,plain,(
% 1.83/0.62    m1_pre_topc(sK2,sK0)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f4034,plain,(
% 1.83/0.62    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | (~spl5_3 | spl5_20)),
% 1.83/0.62    inference(resolution,[],[f4031,f45])).
% 1.83/0.62  fof(f45,plain,(
% 1.83/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f15])).
% 1.83/0.62  fof(f15,plain,(
% 1.83/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.83/0.62    inference(ennf_transformation,[],[f4])).
% 1.83/0.62  fof(f4,axiom,(
% 1.83/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.83/0.62  fof(f4031,plain,(
% 1.83/0.62    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (~spl5_3 | spl5_20)),
% 1.83/0.62    inference(subsumption_resolution,[],[f4028,f228])).
% 1.83/0.62  fof(f228,plain,(
% 1.83/0.62    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl5_20),
% 1.83/0.62    inference(avatar_component_clause,[],[f227])).
% 1.83/0.62  fof(f227,plain,(
% 1.83/0.62    spl5_20 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.83/0.62  fof(f4028,plain,(
% 1.83/0.62    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_3),
% 1.83/0.62    inference(resolution,[],[f98,f47])).
% 1.83/0.62  fof(f47,plain,(
% 1.83/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f18])).
% 1.83/0.62  fof(f18,plain,(
% 1.83/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.83/0.62    inference(flattening,[],[f17])).
% 1.83/0.62  fof(f17,plain,(
% 1.83/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f6])).
% 1.83/0.62  fof(f6,axiom,(
% 1.83/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.83/0.62  fof(f98,plain,(
% 1.83/0.62    v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl5_3),
% 1.83/0.62    inference(avatar_component_clause,[],[f96])).
% 1.83/0.62  fof(f96,plain,(
% 1.83/0.62    spl5_3 <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.83/0.62  fof(f4023,plain,(
% 1.83/0.62    spl5_2 | ~spl5_4 | ~spl5_22),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f4022])).
% 1.83/0.62  fof(f4022,plain,(
% 1.83/0.62    $false | (spl5_2 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f4021,f92])).
% 1.83/0.62  fof(f92,plain,(
% 1.83/0.62    l1_pre_topc(sK2)),
% 1.83/0.62    inference(subsumption_resolution,[],[f88,f37])).
% 1.83/0.62  fof(f88,plain,(
% 1.83/0.62    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.83/0.62    inference(resolution,[],[f41,f46])).
% 1.83/0.62  fof(f4021,plain,(
% 1.83/0.62    ~l1_pre_topc(sK2) | (spl5_2 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f4020,f45])).
% 1.83/0.62  fof(f4020,plain,(
% 1.83/0.62    ~l1_struct_0(sK2) | (spl5_2 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f4018,f40])).
% 1.83/0.62  fof(f4018,plain,(
% 1.83/0.62    ~l1_struct_0(sK2) | v2_struct_0(sK2) | (spl5_2 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f3948,f47])).
% 1.83/0.62  fof(f3948,plain,(
% 1.83/0.62    v1_xboole_0(u1_struct_0(sK2)) | (spl5_2 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f3947,f79])).
% 1.83/0.62  fof(f79,plain,(
% 1.83/0.62    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl5_2),
% 1.83/0.62    inference(avatar_component_clause,[],[f77])).
% 1.83/0.62  fof(f77,plain,(
% 1.83/0.62    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.83/0.62  fof(f3947,plain,(
% 1.83/0.62    m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f3946,f52])).
% 1.83/0.62  fof(f52,plain,(
% 1.83/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f30])).
% 1.83/0.62  fof(f30,plain,(
% 1.83/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.83/0.62    inference(nnf_transformation,[],[f21])).
% 1.83/0.62  fof(f21,plain,(
% 1.83/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f3])).
% 1.83/0.62  fof(f3,axiom,(
% 1.83/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.83/0.62  fof(f3946,plain,(
% 1.83/0.62    r2_hidden(sK3,u1_struct_0(sK2)) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f3945,f1618])).
% 1.83/0.62  fof(f1618,plain,(
% 1.83/0.62    r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f812,f102])).
% 1.83/0.62  fof(f102,plain,(
% 1.83/0.62    r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl5_4),
% 1.83/0.62    inference(avatar_component_clause,[],[f100])).
% 1.83/0.62  fof(f100,plain,(
% 1.83/0.62    spl5_4 <=> r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.83/0.62  fof(f812,plain,(
% 1.83/0.62    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | r2_hidden(X2,u1_struct_0(sK1))) ) | ~spl5_22),
% 1.83/0.62    inference(superposition,[],[f71,f237])).
% 1.83/0.62  fof(f237,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_22),
% 1.83/0.62    inference(avatar_component_clause,[],[f235])).
% 1.83/0.62  fof(f235,plain,(
% 1.83/0.62    spl5_22 <=> u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.83/0.62  fof(f71,plain,(
% 1.83/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.83/0.62    inference(equality_resolution,[],[f58])).
% 1.83/0.62  fof(f58,plain,(
% 1.83/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.83/0.62    inference(cnf_transformation,[],[f35])).
% 1.83/0.62  fof(f35,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.83/0.62  fof(f34,plain,(
% 1.83/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.83/0.62    introduced(choice_axiom,[])).
% 1.83/0.62  fof(f33,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(rectify,[],[f32])).
% 1.83/0.62  fof(f32,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(flattening,[],[f31])).
% 1.83/0.62  fof(f31,plain,(
% 1.83/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.83/0.62    inference(nnf_transformation,[],[f1])).
% 1.83/0.62  fof(f1,axiom,(
% 1.83/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.83/0.62  fof(f3945,plain,(
% 1.83/0.62    r2_hidden(sK3,u1_struct_0(sK2)) | ~r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f3944,f69])).
% 1.83/0.62  fof(f69,plain,(
% 1.83/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.83/0.62    inference(equality_resolution,[],[f60])).
% 1.83/0.62  fof(f60,plain,(
% 1.83/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.83/0.62    inference(cnf_transformation,[],[f35])).
% 1.83/0.62  fof(f3944,plain,(
% 1.83/0.62    ~r2_hidden(sK3,k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f813,f102])).
% 1.83/0.62  fof(f813,plain,(
% 1.83/0.62    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~r2_hidden(X3,k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))) ) | ~spl5_22),
% 1.83/0.62    inference(superposition,[],[f70,f237])).
% 1.83/0.62  fof(f70,plain,(
% 1.83/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.83/0.62    inference(equality_resolution,[],[f59])).
% 1.83/0.62  fof(f59,plain,(
% 1.83/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.83/0.62    inference(cnf_transformation,[],[f35])).
% 1.83/0.62  fof(f1695,plain,(
% 1.83/0.62    spl5_1 | ~spl5_4 | ~spl5_22),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f1694])).
% 1.83/0.62  fof(f1694,plain,(
% 1.83/0.62    $false | (spl5_1 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f1693,f86])).
% 1.83/0.62  fof(f86,plain,(
% 1.83/0.62    l1_pre_topc(sK1)),
% 1.83/0.62    inference(subsumption_resolution,[],[f82,f37])).
% 1.83/0.62  fof(f82,plain,(
% 1.83/0.62    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.83/0.62    inference(resolution,[],[f39,f46])).
% 1.83/0.62  fof(f1693,plain,(
% 1.83/0.62    ~l1_pre_topc(sK1) | (spl5_1 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f1623,f45])).
% 1.83/0.62  fof(f1623,plain,(
% 1.83/0.62    ~l1_struct_0(sK1) | (spl5_1 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f1621,f38])).
% 1.83/0.62  fof(f1621,plain,(
% 1.83/0.62    ~l1_struct_0(sK1) | v2_struct_0(sK1) | (spl5_1 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f1620,f47])).
% 1.83/0.62  fof(f1620,plain,(
% 1.83/0.62    v1_xboole_0(u1_struct_0(sK1)) | (spl5_1 | ~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(subsumption_resolution,[],[f1619,f75])).
% 1.83/0.62  fof(f75,plain,(
% 1.83/0.62    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl5_1),
% 1.83/0.62    inference(avatar_component_clause,[],[f73])).
% 1.83/0.62  fof(f73,plain,(
% 1.83/0.62    spl5_1 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.83/0.62  fof(f1619,plain,(
% 1.83/0.62    m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl5_4 | ~spl5_22)),
% 1.83/0.62    inference(resolution,[],[f1618,f52])).
% 1.83/0.62  fof(f338,plain,(
% 1.83/0.62    spl5_21),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f337])).
% 1.83/0.62  fof(f337,plain,(
% 1.83/0.62    $false | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f336,f36])).
% 1.83/0.62  fof(f336,plain,(
% 1.83/0.62    v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f335,f37])).
% 1.83/0.62  fof(f335,plain,(
% 1.83/0.62    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f334,f38])).
% 1.83/0.62  fof(f334,plain,(
% 1.83/0.62    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f333,f39])).
% 1.83/0.62  fof(f333,plain,(
% 1.83/0.62    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f332,f40])).
% 1.83/0.62  fof(f332,plain,(
% 1.83/0.62    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(subsumption_resolution,[],[f331,f41])).
% 1.83/0.62  fof(f331,plain,(
% 1.83/0.62    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_21),
% 1.83/0.62    inference(resolution,[],[f233,f56])).
% 1.83/0.62  fof(f56,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f23])).
% 1.83/0.62  fof(f233,plain,(
% 1.83/0.62    ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl5_21),
% 1.83/0.62    inference(avatar_component_clause,[],[f231])).
% 1.83/0.62  fof(f231,plain,(
% 1.83/0.62    spl5_21 <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 1.83/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.83/0.62  fof(f330,plain,(
% 1.83/0.62    ~spl5_20),
% 1.83/0.62    inference(avatar_contradiction_clause,[],[f329])).
% 1.83/0.62  fof(f329,plain,(
% 1.83/0.62    $false | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f328,f36])).
% 1.83/0.62  fof(f328,plain,(
% 1.83/0.62    v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f327,f37])).
% 1.83/0.62  fof(f327,plain,(
% 1.83/0.62    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f326,f38])).
% 1.83/0.62  fof(f326,plain,(
% 1.83/0.62    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f325,f39])).
% 1.83/0.62  fof(f325,plain,(
% 1.83/0.62    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f324,f40])).
% 1.83/0.62  fof(f324,plain,(
% 1.83/0.62    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(subsumption_resolution,[],[f323,f41])).
% 1.83/0.62  fof(f323,plain,(
% 1.83/0.62    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_20),
% 1.83/0.62    inference(resolution,[],[f229,f55])).
% 1.83/0.62  fof(f55,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f23])).
% 1.83/0.62  fof(f229,plain,(
% 1.83/0.62    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_20),
% 1.83/0.62    inference(avatar_component_clause,[],[f227])).
% 1.83/0.62  fof(f238,plain,(
% 1.83/0.62    spl5_20 | ~spl5_21 | spl5_22),
% 1.83/0.62    inference(avatar_split_clause,[],[f225,f235,f231,f227])).
% 1.83/0.62  fof(f225,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.83/0.62    inference(subsumption_resolution,[],[f224,f36])).
% 1.83/0.62  fof(f224,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f223,f37])).
% 1.83/0.62  fof(f223,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f222,f38])).
% 1.83/0.62  fof(f222,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f221,f39])).
% 1.83/0.62  fof(f221,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f220,f40])).
% 1.83/0.62  fof(f220,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f219,f41])).
% 1.83/0.62  fof(f219,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(subsumption_resolution,[],[f214,f42])).
% 1.83/0.62  fof(f42,plain,(
% 1.83/0.62    ~r1_tsep_1(sK1,sK2)),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f214,plain,(
% 1.83/0.62    u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) = k4_xboole_0(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.83/0.62    inference(resolution,[],[f116,f68])).
% 1.83/0.62  fof(f68,plain,(
% 1.83/0.62    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(equality_resolution,[],[f65])).
% 1.83/0.62  fof(f65,plain,(
% 1.83/0.62    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k4_xboole_0(u1_struct_0(X1),k4_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(definition_unfolding,[],[f48,f50])).
% 1.83/0.62  fof(f50,plain,(
% 1.83/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f2])).
% 1.83/0.62  fof(f2,axiom,(
% 1.83/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.83/0.62  fof(f48,plain,(
% 1.83/0.62    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f29])).
% 1.83/0.62  fof(f29,plain,(
% 1.83/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.62    inference(nnf_transformation,[],[f20])).
% 1.83/0.62  fof(f20,plain,(
% 1.83/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.83/0.62    inference(flattening,[],[f19])).
% 1.83/0.62  fof(f19,plain,(
% 1.83/0.62    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.83/0.62    inference(ennf_transformation,[],[f7])).
% 1.83/0.62  fof(f7,axiom,(
% 1.83/0.62    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.83/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.83/0.62  fof(f103,plain,(
% 1.83/0.62    spl5_3 | spl5_4),
% 1.83/0.62    inference(avatar_split_clause,[],[f93,f100,f96])).
% 1.83/0.62  fof(f93,plain,(
% 1.83/0.62    r2_hidden(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.83/0.62    inference(resolution,[],[f43,f51])).
% 1.83/0.62  fof(f51,plain,(
% 1.83/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.83/0.62    inference(cnf_transformation,[],[f30])).
% 1.83/0.62  fof(f43,plain,(
% 1.83/0.62    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  fof(f80,plain,(
% 1.83/0.62    ~spl5_1 | ~spl5_2),
% 1.83/0.62    inference(avatar_split_clause,[],[f67,f77,f73])).
% 1.83/0.62  fof(f67,plain,(
% 1.83/0.62    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.83/0.62    inference(equality_resolution,[],[f66])).
% 1.83/0.62  fof(f66,plain,(
% 1.83/0.62    ( ! [X5] : (~m1_subset_1(sK3,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.83/0.62    inference(equality_resolution,[],[f44])).
% 1.83/0.62  fof(f44,plain,(
% 1.83/0.62    ( ! [X4,X5] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.83/0.62    inference(cnf_transformation,[],[f28])).
% 1.83/0.62  % SZS output end Proof for theBenchmark
% 1.83/0.62  % (13251)------------------------------
% 1.83/0.62  % (13251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.62  % (13251)Termination reason: Refutation
% 1.83/0.62  
% 1.83/0.62  % (13251)Memory used [KB]: 13048
% 1.83/0.62  % (13251)Time elapsed: 0.209 s
% 1.83/0.62  % (13251)------------------------------
% 1.83/0.62  % (13251)------------------------------
% 2.09/0.63  % (13242)Success in time 0.271 s
%------------------------------------------------------------------------------

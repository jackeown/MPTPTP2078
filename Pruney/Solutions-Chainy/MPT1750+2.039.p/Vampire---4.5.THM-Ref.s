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
% DateTime   : Thu Dec  3 13:18:20 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 875 expanded)
%              Number of leaves         :   29 ( 361 expanded)
%              Depth                    :   24
%              Number of atoms          :  785 (9371 expanded)
%              Number of equality atoms :   55 ( 878 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f695,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f218,f231,f242,f272,f578,f679,f694])).

fof(f694,plain,
    ( ~ spl5_2
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f692,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2))
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2))
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f692,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f691,f100])).

fof(f100,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f58,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f691,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(resolution,[],[f690,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f690,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f689,f134])).

fof(f134,plain,(
    sP4(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f133,f64])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f133,plain,
    ( ~ v1_funct_1(sK3)
    | sP4(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f122,f65])).

fof(f65,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | sP4(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f66,f97])).

fof(f97,plain,(
    ! [X2,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | sP4(X3,X2) ) ),
    inference(cnf_transformation,[],[f97_D])).

fof(f97_D,plain,(
    ! [X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          | ~ v1_funct_2(X5,X2,X3)
          | ~ v1_funct_1(X5) )
    <=> ~ sP4(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f689,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ sP4(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f688,f64])).

fof(f688,plain,
    ( ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ sP4(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f687,f65])).

fof(f687,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ sP4(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f686,f66])).

fof(f686,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ sP4(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ sP4(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(resolution,[],[f684,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | ~ sP4(X3,X2) ) ),
    inference(general_splitting,[],[f91,f97_D])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f684,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ spl5_2
    | ~ spl5_26 ),
    inference(backward_demodulation,[],[f276,f577])).

fof(f577,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f575])).

fof(f575,plain,
    ( spl5_26
  <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f276,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f68,f116])).

fof(f116,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_2
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f68,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f679,plain,
    ( ~ spl5_2
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | ~ spl5_2
    | spl5_25 ),
    inference(subsumption_resolution,[],[f660,f573])).

fof(f573,plain,
    ( ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl5_25
  <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f660,plain,
    ( r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f410,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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

fof(f410,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f409,f64])).

fof(f409,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f407,f66])).

fof(f407,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(superposition,[],[f88,f342])).

fof(f342,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f336,f116])).

fof(f336,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f131,f63])).

% (1951)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (1959)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (1936)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (1947)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f63,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f130,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f129,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f128,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f127,f56])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f126,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f126,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f125,f58])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f124,f64])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f118,f65])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f66,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f578,plain,
    ( ~ spl5_25
    | spl5_26
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f568,f114,f575,f571])).

fof(f568,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f350,f414])).

fof(f414,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f413,f64])).

fof(f413,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f412,f65])).

fof(f412,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f411,f66])).

fof(f411,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f408,f95])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f408,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(superposition,[],[f86,f342])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f350,plain,(
    ! [X0] :
      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)
      | sK3 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f119,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | sK3 = X1
      | ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X1,sK3) ) ),
    inference(resolution,[],[f66,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f272,plain,
    ( spl5_1
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl5_1
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f270,f112])).

fof(f112,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_1
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f270,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(resolution,[],[f269,f84])).

fof(f269,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f267,f105])).

fof(f105,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f103,f61])).

fof(f103,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f63,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f267,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(resolution,[],[f265,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f265,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f264,f105])).

fof(f264,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f263,f163])).

fof(f163,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_6
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f263,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f262,f180])).

fof(f180,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_8
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f262,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f261,f60])).

fof(f261,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f258,f61])).

fof(f258,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ spl5_11 ),
    inference(resolution,[],[f224,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f224,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_11
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f242,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f240,f60])).

fof(f240,plain,
    ( ~ v2_pre_topc(sK1)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f239,f61])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl5_6 ),
    inference(resolution,[],[f162,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f162,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f231,plain,
    ( spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f230,f179,f222])).

fof(f230,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    inference(global_subsumption,[],[f220])).

fof(f220,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f219,f61])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f204,f63])).

fof(f204,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f147,f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f154,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f154,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X3,sK2) ) ),
    inference(subsumption_resolution,[],[f148,f105])).

fof(f148,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X3,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f75,f67])).

fof(f67,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f147,plain,(
    ! [X2] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f74,f67])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f218,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f213,f105])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_8 ),
    inference(resolution,[],[f208,f197])).

fof(f197,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f192,f105])).

fof(f192,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f176,f63])).

fof(f208,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(sK2,X4)
        | ~ l1_pre_topc(X4) )
    | spl5_8 ),
    inference(subsumption_resolution,[],[f205,f181])).

fof(f181,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f205,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(sK2,X4)
      | ~ l1_pre_topc(X4)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f147,f72])).

fof(f117,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f107,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f104,f84])).

fof(f104,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f102,f61])).

fof(f102,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f63,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (1935)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (1952)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.48  % (1949)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (1937)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (1934)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (1942)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (1940)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (1938)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (1945)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (1946)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.22/0.52  % (1955)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.22/0.52  % (1933)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.22/0.52  % (1954)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.22/0.52  % (1957)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.22/0.52  % (1934)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f695,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(avatar_sat_refutation,[],[f117,f218,f231,f242,f272,f578,f679,f694])).
% 1.22/0.52  fof(f694,plain,(
% 1.22/0.52    ~spl5_2 | ~spl5_26),
% 1.22/0.52    inference(avatar_contradiction_clause,[],[f693])).
% 1.22/0.52  fof(f693,plain,(
% 1.22/0.52    $false | (~spl5_2 | ~spl5_26)),
% 1.22/0.52    inference(subsumption_resolution,[],[f692,f56])).
% 1.22/0.52  fof(f56,plain,(
% 1.22/0.52    ~v2_struct_0(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f49])).
% 1.22/0.52  fof(f49,plain,(
% 1.22/0.52    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47,f46,f45])).
% 1.22/0.52  fof(f45,plain,(
% 1.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f46,plain,(
% 1.22/0.52    ? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f47,plain,(
% 1.22/0.52    ? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f48,plain,(
% 1.22/0.52    ? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),X3,k2_tmap_1(sK1,sK0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 1.22/0.52    introduced(choice_axiom,[])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.22/0.52    inference(flattening,[],[f21])).
% 1.22/0.52  fof(f21,plain,(
% 1.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f18])).
% 1.22/0.52  fof(f18,negated_conjecture,(
% 1.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 1.22/0.52    inference(negated_conjecture,[],[f17])).
% 1.22/0.52  fof(f17,conjecture,(
% 1.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).
% 1.22/0.52  fof(f692,plain,(
% 1.22/0.52    v2_struct_0(sK0) | (~spl5_2 | ~spl5_26)),
% 1.22/0.52    inference(subsumption_resolution,[],[f691,f100])).
% 1.22/0.52  fof(f100,plain,(
% 1.22/0.52    l1_struct_0(sK0)),
% 1.22/0.52    inference(resolution,[],[f58,f69])).
% 1.22/0.52  fof(f69,plain,(
% 1.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f23])).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.22/0.52  fof(f58,plain,(
% 1.22/0.52    l1_pre_topc(sK0)),
% 1.22/0.52    inference(cnf_transformation,[],[f49])).
% 1.22/0.52  fof(f691,plain,(
% 1.22/0.52    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_26)),
% 1.22/0.52    inference(resolution,[],[f690,f78])).
% 1.22/0.52  fof(f78,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f32])).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.22/0.52    inference(flattening,[],[f31])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.22/0.52    inference(ennf_transformation,[],[f8])).
% 1.22/0.52  fof(f8,axiom,(
% 1.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.22/0.52  fof(f690,plain,(
% 1.22/0.52    v1_xboole_0(u1_struct_0(sK0)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.52    inference(subsumption_resolution,[],[f689,f134])).
% 1.22/0.52  fof(f134,plain,(
% 1.22/0.52    sP4(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.22/0.52    inference(subsumption_resolution,[],[f133,f64])).
% 1.22/0.53  fof(f64,plain,(
% 1.22/0.53    v1_funct_1(sK3)),
% 1.22/0.53    inference(cnf_transformation,[],[f49])).
% 1.22/0.53  fof(f133,plain,(
% 1.22/0.53    ~v1_funct_1(sK3) | sP4(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.22/0.53    inference(subsumption_resolution,[],[f122,f65])).
% 1.22/0.53  fof(f65,plain,(
% 1.22/0.53    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.22/0.53    inference(cnf_transformation,[],[f49])).
% 1.22/0.53  fof(f122,plain,(
% 1.22/0.53    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | sP4(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.22/0.53    inference(resolution,[],[f66,f97])).
% 1.22/0.53  fof(f97,plain,(
% 1.22/0.53    ( ! [X2,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | sP4(X3,X2)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f97_D])).
% 1.22/0.53  fof(f97_D,plain,(
% 1.22/0.53    ( ! [X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5)) ) <=> ~sP4(X3,X2)) )),
% 1.22/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 1.22/0.53  fof(f66,plain,(
% 1.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.22/0.53    inference(cnf_transformation,[],[f49])).
% 1.22/0.53  fof(f689,plain,(
% 1.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~sP4(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(subsumption_resolution,[],[f688,f64])).
% 1.22/0.53  fof(f688,plain,(
% 1.22/0.53    ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~sP4(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(subsumption_resolution,[],[f687,f65])).
% 1.22/0.53  fof(f687,plain,(
% 1.22/0.53    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~sP4(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(subsumption_resolution,[],[f686,f66])).
% 1.22/0.53  fof(f686,plain,(
% 1.22/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~sP4(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(duplicate_literal_removal,[],[f685])).
% 1.22/0.53  fof(f685,plain,(
% 1.22/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~sP4(u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(resolution,[],[f684,f98])).
% 1.22/0.53  fof(f98,plain,(
% 1.22/0.53    ( ! [X4,X2,X0,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1) | ~sP4(X3,X2)) )),
% 1.22/0.53    inference(general_splitting,[],[f91,f97_D])).
% 1.22/0.53  fof(f91,plain,(
% 1.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f44])).
% 1.22/0.53  fof(f44,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.22/0.53    inference(flattening,[],[f43])).
% 1.22/0.53  fof(f43,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.22/0.53    inference(ennf_transformation,[],[f12])).
% 1.22/0.53  fof(f12,axiom,(
% 1.22/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 1.22/0.53  fof(f684,plain,(
% 1.22/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) | (~spl5_2 | ~spl5_26)),
% 1.22/0.53    inference(backward_demodulation,[],[f276,f577])).
% 1.22/0.53  fof(f577,plain,(
% 1.22/0.53    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | ~spl5_26),
% 1.22/0.53    inference(avatar_component_clause,[],[f575])).
% 1.22/0.53  fof(f575,plain,(
% 1.22/0.53    spl5_26 <=> sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.22/0.53  fof(f276,plain,(
% 1.22/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | ~spl5_2),
% 1.22/0.53    inference(backward_demodulation,[],[f68,f116])).
% 1.22/0.53  fof(f116,plain,(
% 1.22/0.53    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl5_2),
% 1.22/0.53    inference(avatar_component_clause,[],[f114])).
% 1.22/0.53  fof(f114,plain,(
% 1.22/0.53    spl5_2 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.22/0.53  fof(f68,plain,(
% 1.22/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 1.22/0.53    inference(cnf_transformation,[],[f49])).
% 1.22/0.53  fof(f679,plain,(
% 1.22/0.53    ~spl5_2 | spl5_25),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f678])).
% 1.22/0.53  fof(f678,plain,(
% 1.22/0.53    $false | (~spl5_2 | spl5_25)),
% 1.22/0.53    inference(subsumption_resolution,[],[f660,f573])).
% 1.22/0.53  fof(f573,plain,(
% 1.22/0.53    ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | spl5_25),
% 1.22/0.53    inference(avatar_component_clause,[],[f571])).
% 1.22/0.53  fof(f571,plain,(
% 1.22/0.53    spl5_25 <=> r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.22/0.53  fof(f660,plain,(
% 1.22/0.53    r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~spl5_2),
% 1.22/0.53    inference(resolution,[],[f410,f84])).
% 1.22/0.53  fof(f84,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f54])).
% 1.22/0.53  fof(f54,plain,(
% 1.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.22/0.53    inference(nnf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.22/0.53  fof(f410,plain,(
% 1.22/0.53    m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_2),
% 1.22/0.53    inference(subsumption_resolution,[],[f409,f64])).
% 1.22/0.53  fof(f409,plain,(
% 1.22/0.53    m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.22/0.53    inference(subsumption_resolution,[],[f407,f66])).
% 1.22/0.53  fof(f407,plain,(
% 1.22/0.53    m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.22/0.53    inference(superposition,[],[f88,f342])).
% 1.22/0.53  fof(f342,plain,(
% 1.22/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) | ~spl5_2),
% 1.22/0.53    inference(forward_demodulation,[],[f336,f116])).
% 1.22/0.54  fof(f336,plain,(
% 1.22/0.54    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))),
% 1.22/0.54    inference(resolution,[],[f131,f63])).
% 1.22/0.54  % (1951)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.22/0.54  % (1959)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.22/0.54  % (1936)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.45/0.54  % (1947)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.55  fof(f63,plain,(
% 1.45/0.55    m1_pre_topc(sK2,sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f131,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f130,f59])).
% 1.45/0.55  fof(f59,plain,(
% 1.45/0.55    ~v2_struct_0(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f130,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f129,f60])).
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    v2_pre_topc(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f129,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f128,f61])).
% 1.45/0.55  fof(f61,plain,(
% 1.45/0.55    l1_pre_topc(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f128,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f127,f56])).
% 1.45/0.55  fof(f127,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f126,f57])).
% 1.45/0.55  fof(f57,plain,(
% 1.45/0.55    v2_pre_topc(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f126,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f125,f58])).
% 1.45/0.55  fof(f125,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f124,f64])).
% 1.45/0.55  fof(f124,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f118,f65])).
% 1.45/0.55  fof(f118,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.45/0.55    inference(resolution,[],[f66,f79])).
% 1.45/0.55  fof(f79,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f34])).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f33])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f13])).
% 1.45/0.55  fof(f13,axiom,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.45/0.55  fof(f88,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f40])).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.45/0.55    inference(flattening,[],[f39])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.45/0.55    inference(ennf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.45/0.55  fof(f578,plain,(
% 1.45/0.55    ~spl5_25 | spl5_26 | ~spl5_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f568,f114,f575,f571])).
% 1.45/0.55  fof(f568,plain,(
% 1.45/0.55    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | ~r1_tarski(k2_tmap_1(sK1,sK0,sK3,sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | ~spl5_2),
% 1.45/0.55    inference(resolution,[],[f350,f414])).
% 1.45/0.55  fof(f414,plain,(
% 1.45/0.55    r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~spl5_2),
% 1.45/0.55    inference(subsumption_resolution,[],[f413,f64])).
% 1.45/0.55  fof(f413,plain,(
% 1.45/0.55    r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.45/0.55    inference(subsumption_resolution,[],[f412,f65])).
% 1.45/0.55  fof(f412,plain,(
% 1.45/0.55    r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.45/0.55    inference(subsumption_resolution,[],[f411,f66])).
% 1.45/0.55  fof(f411,plain,(
% 1.45/0.55    r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.45/0.55    inference(subsumption_resolution,[],[f408,f95])).
% 1.45/0.55  fof(f95,plain,(
% 1.45/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.55    inference(equality_resolution,[],[f81])).
% 1.45/0.55  fof(f81,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f53])).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.55    inference(flattening,[],[f52])).
% 1.45/0.55  fof(f52,plain,(
% 1.45/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.55    inference(nnf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.55  fof(f408,plain,(
% 1.45/0.55    r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK3) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | ~spl5_2),
% 1.45/0.55    inference(superposition,[],[f86,f342])).
% 1.45/0.55  fof(f86,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f38])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.45/0.55    inference(flattening,[],[f37])).
% 1.45/0.55  fof(f37,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.45/0.55    inference(ennf_transformation,[],[f5])).
% 1.45/0.55  fof(f5,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).
% 1.45/0.55  fof(f350,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3) | sK3 = X0 | ~r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )),
% 1.45/0.55    inference(resolution,[],[f119,f85])).
% 1.45/0.55  fof(f85,plain,(
% 1.45/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f54])).
% 1.45/0.55  fof(f119,plain,(
% 1.45/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | sK3 = X1 | ~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X1,sK3)) )),
% 1.45/0.55    inference(resolution,[],[f66,f89])).
% 1.45/0.55  fof(f89,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.55    inference(cnf_transformation,[],[f55])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(nnf_transformation,[],[f42])).
% 1.45/0.55  fof(f42,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.55    inference(flattening,[],[f41])).
% 1.45/0.55  fof(f41,plain,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.45/0.55    inference(ennf_transformation,[],[f3])).
% 1.45/0.55  fof(f3,axiom,(
% 1.45/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.45/0.55  fof(f272,plain,(
% 1.45/0.55    spl5_1 | ~spl5_6 | ~spl5_8 | ~spl5_11),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f271])).
% 1.45/0.55  fof(f271,plain,(
% 1.45/0.55    $false | (spl5_1 | ~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(subsumption_resolution,[],[f270,f112])).
% 1.45/0.55  fof(f112,plain,(
% 1.45/0.55    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | spl5_1),
% 1.45/0.55    inference(avatar_component_clause,[],[f110])).
% 1.45/0.55  fof(f110,plain,(
% 1.45/0.55    spl5_1 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.45/0.55  fof(f270,plain,(
% 1.45/0.55    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(resolution,[],[f269,f84])).
% 1.45/0.55  fof(f269,plain,(
% 1.45/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(subsumption_resolution,[],[f267,f105])).
% 1.45/0.55  fof(f105,plain,(
% 1.45/0.55    l1_pre_topc(sK2)),
% 1.45/0.55    inference(subsumption_resolution,[],[f103,f61])).
% 1.45/0.55  fof(f103,plain,(
% 1.45/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 1.45/0.55    inference(resolution,[],[f63,f72])).
% 1.45/0.55  fof(f72,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.45/0.55  fof(f267,plain,(
% 1.45/0.55    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | (~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(resolution,[],[f265,f73])).
% 1.45/0.55  fof(f73,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f26])).
% 1.45/0.55  fof(f26,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f16])).
% 1.45/0.55  fof(f16,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.45/0.55  fof(f265,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | (~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(subsumption_resolution,[],[f264,f105])).
% 1.45/0.55  fof(f264,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | ~l1_pre_topc(sK2) | (~spl5_6 | ~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(subsumption_resolution,[],[f263,f163])).
% 1.45/0.55  fof(f163,plain,(
% 1.45/0.55    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_6),
% 1.45/0.55    inference(avatar_component_clause,[],[f161])).
% 1.45/0.55  fof(f161,plain,(
% 1.45/0.55    spl5_6 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.45/0.55  fof(f263,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | (~spl5_8 | ~spl5_11)),
% 1.45/0.55    inference(subsumption_resolution,[],[f262,f180])).
% 1.45/0.55  fof(f180,plain,(
% 1.45/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_8),
% 1.45/0.55    inference(avatar_component_clause,[],[f179])).
% 1.45/0.55  fof(f179,plain,(
% 1.45/0.55    spl5_8 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.45/0.55  fof(f262,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | ~spl5_11),
% 1.45/0.55    inference(subsumption_resolution,[],[f261,f60])).
% 1.45/0.55  fof(f261,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | ~spl5_11),
% 1.45/0.55    inference(subsumption_resolution,[],[f258,f61])).
% 1.45/0.55  fof(f258,plain,(
% 1.45/0.55    m1_pre_topc(sK1,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK2) | ~spl5_11),
% 1.45/0.55    inference(resolution,[],[f224,f93])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    ( ! [X2,X0] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(equality_resolution,[],[f76])).
% 1.45/0.55  fof(f76,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f51])).
% 1.45/0.55  fof(f51,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(nnf_transformation,[],[f30])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(flattening,[],[f29])).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f15])).
% 1.45/0.55  fof(f15,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 1.45/0.55  fof(f224,plain,(
% 1.45/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl5_11),
% 1.45/0.55    inference(avatar_component_clause,[],[f222])).
% 1.45/0.55  fof(f222,plain,(
% 1.45/0.55    spl5_11 <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.45/0.55  fof(f242,plain,(
% 1.45/0.55    spl5_6),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f241])).
% 1.45/0.55  fof(f241,plain,(
% 1.45/0.55    $false | spl5_6),
% 1.45/0.55    inference(subsumption_resolution,[],[f240,f60])).
% 1.45/0.55  fof(f240,plain,(
% 1.45/0.55    ~v2_pre_topc(sK1) | spl5_6),
% 1.45/0.55    inference(subsumption_resolution,[],[f239,f61])).
% 1.45/0.55  fof(f239,plain,(
% 1.45/0.55    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl5_6),
% 1.45/0.55    inference(resolution,[],[f162,f80])).
% 1.45/0.55  fof(f80,plain,(
% 1.45/0.55    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f36])).
% 1.45/0.55  fof(f36,plain,(
% 1.45/0.55    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.55    inference(flattening,[],[f35])).
% 1.45/0.55  fof(f35,plain,(
% 1.45/0.55    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f20])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 1.45/0.55    inference(pure_predicate_removal,[],[f9])).
% 1.45/0.55  fof(f9,axiom,(
% 1.45/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 1.45/0.55  fof(f162,plain,(
% 1.45/0.55    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_6),
% 1.45/0.55    inference(avatar_component_clause,[],[f161])).
% 1.45/0.55  fof(f231,plain,(
% 1.45/0.55    spl5_11 | ~spl5_8),
% 1.45/0.55    inference(avatar_split_clause,[],[f230,f179,f222])).
% 1.45/0.55  fof(f230,plain,(
% 1.45/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),
% 1.45/0.55    inference(global_subsumption,[],[f220])).
% 1.45/0.55  fof(f220,plain,(
% 1.45/0.55    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.45/0.55    inference(subsumption_resolution,[],[f219,f61])).
% 1.45/0.55  fof(f219,plain,(
% 1.45/0.55    ~l1_pre_topc(sK1) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.45/0.55    inference(subsumption_resolution,[],[f204,f63])).
% 1.45/0.55  fof(f204,plain,(
% 1.45/0.55    ~m1_pre_topc(sK2,sK1) | ~l1_pre_topc(sK1) | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.45/0.55    inference(resolution,[],[f147,f176])).
% 1.45/0.55  fof(f176,plain,(
% 1.45/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK1) | m1_pre_topc(X0,sK2) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f173,f61])).
% 1.45/0.55  fof(f173,plain,(
% 1.45/0.55    ( ! [X0] : (m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(resolution,[],[f154,f70])).
% 1.45/0.55  fof(f70,plain,(
% 1.45/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f50])).
% 1.45/0.55  fof(f50,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(nnf_transformation,[],[f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f11])).
% 1.45/0.55  fof(f11,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.45/0.55  fof(f154,plain,(
% 1.45/0.55    ( ! [X3] : (~m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X3,sK2)) )),
% 1.45/0.55    inference(subsumption_resolution,[],[f148,f105])).
% 1.45/0.55  fof(f148,plain,(
% 1.45/0.55    ( ! [X3] : (~m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X3,sK2) | ~l1_pre_topc(sK2)) )),
% 1.45/0.55    inference(superposition,[],[f75,f67])).
% 1.45/0.55  fof(f67,plain,(
% 1.45/0.55    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.45/0.55    inference(cnf_transformation,[],[f49])).
% 1.45/0.55  fof(f75,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f28])).
% 1.45/0.55  fof(f28,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.45/0.55  fof(f147,plain,(
% 1.45/0.55    ( ! [X2] : (m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2)) )),
% 1.45/0.55    inference(superposition,[],[f74,f67])).
% 1.45/0.55  fof(f74,plain,(
% 1.45/0.55    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f27])).
% 1.45/0.55  fof(f27,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f19])).
% 1.45/0.55  fof(f19,plain,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 1.45/0.55    inference(pure_predicate_removal,[],[f14])).
% 1.45/0.55  fof(f14,axiom,(
% 1.45/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.45/0.55  fof(f218,plain,(
% 1.45/0.55    spl5_8),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f217])).
% 1.45/0.55  fof(f217,plain,(
% 1.45/0.55    $false | spl5_8),
% 1.45/0.55    inference(subsumption_resolution,[],[f213,f105])).
% 1.45/0.55  fof(f213,plain,(
% 1.45/0.55    ~l1_pre_topc(sK2) | spl5_8),
% 1.45/0.55    inference(resolution,[],[f208,f197])).
% 1.45/0.55  fof(f197,plain,(
% 1.45/0.55    m1_pre_topc(sK2,sK2)),
% 1.45/0.55    inference(subsumption_resolution,[],[f192,f105])).
% 1.45/0.55  fof(f192,plain,(
% 1.45/0.55    m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2)),
% 1.45/0.55    inference(resolution,[],[f176,f63])).
% 1.45/0.55  fof(f208,plain,(
% 1.45/0.55    ( ! [X4] : (~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4)) ) | spl5_8),
% 1.45/0.55    inference(subsumption_resolution,[],[f205,f181])).
% 1.45/0.55  fof(f181,plain,(
% 1.45/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_8),
% 1.45/0.55    inference(avatar_component_clause,[],[f179])).
% 1.45/0.55  fof(f205,plain,(
% 1.45/0.55    ( ! [X4] : (~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) )),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f203])).
% 1.45/0.55  fof(f203,plain,(
% 1.45/0.55    ( ! [X4] : (~m1_pre_topc(sK2,X4) | ~l1_pre_topc(X4) | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X4)) )),
% 1.45/0.55    inference(resolution,[],[f147,f72])).
% 1.45/0.55  fof(f117,plain,(
% 1.45/0.55    ~spl5_1 | spl5_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f108,f114,f110])).
% 1.45/0.55  fof(f108,plain,(
% 1.45/0.55    u1_struct_0(sK1) = u1_struct_0(sK2) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.45/0.55    inference(resolution,[],[f107,f83])).
% 1.45/0.55  fof(f83,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f53])).
% 1.45/0.55  fof(f107,plain,(
% 1.45/0.55    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.45/0.55    inference(resolution,[],[f104,f84])).
% 1.45/0.55  fof(f104,plain,(
% 1.45/0.55    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.45/0.55    inference(subsumption_resolution,[],[f102,f61])).
% 1.45/0.55  fof(f102,plain,(
% 1.45/0.55    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.45/0.55    inference(resolution,[],[f63,f73])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (1934)------------------------------
% 1.45/0.55  % (1934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (1934)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (1934)Memory used [KB]: 11001
% 1.45/0.55  % (1934)Time elapsed: 0.119 s
% 1.45/0.55  % (1934)------------------------------
% 1.45/0.55  % (1934)------------------------------
% 1.45/0.55  % (1950)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.45/0.55  % (1932)Success in time 0.196 s
% 1.45/0.55  % (1939)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.45/0.55  % (1943)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.55  % (1941)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.45/0.55  % (1956)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.45/0.55  % (1953)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
%------------------------------------------------------------------------------

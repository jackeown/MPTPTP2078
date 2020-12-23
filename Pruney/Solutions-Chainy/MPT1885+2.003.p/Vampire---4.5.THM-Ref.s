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
% DateTime   : Thu Dec  3 13:22:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 958 expanded)
%              Number of leaves         :   11 ( 313 expanded)
%              Depth                    :   29
%              Number of atoms          :  484 (9422 expanded)
%              Number of equality atoms :   58 ( 960 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f63,f128])).

fof(f128,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f127,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK5(X0,X1)) = X1
            & m1_pre_topc(sK5(X0,X1),X0)
            & v1_pre_topc(sK5(X0,X1))
            & ~ v2_struct_0(sK5(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK5(X0,X1)) = X1
        & m1_pre_topc(sK5(X0,X1),X0)
        & v1_pre_topc(sK5(X0,X1))
        & ~ v2_struct_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f127,plain,(
    v2_struct_0(sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f37,f36,f63,f126])).

fof(f126,plain,
    ( v2_struct_0(sK5(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f125,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_pre_topc(sK5(sK2,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(global_subsumption,[],[f35,f33,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK2)
      | m1_pre_topc(sK5(sK2,X0),sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK5(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f125,plain,
    ( ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(resolution,[],[f123,f110])).

fof(f110,plain,
    ( ~ v4_tex_2(sK5(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f92,f109])).

fof(f109,plain,
    ( ~ v4_tex_2(sK5(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | ~ v1_pre_topc(sK5(sK2,sK3))
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( sK3 != sK3
    | ~ v4_tex_2(sK5(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | ~ v1_pre_topc(sK5(sK2,sK3))
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(superposition,[],[f39,f101])).

fof(f101,plain,(
    sK3 = u1_struct_0(sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f36,f63,f98])).

fof(f98,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK3)
    | sK3 = u1_struct_0(sK5(sK2,sK3)) ),
    inference(resolution,[],[f97,f37])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X0,sK2)
      | v1_xboole_0(X0)
      | u1_struct_0(sK5(sK2,X0)) = X0 ) ),
    inference(global_subsumption,[],[f35,f33,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK2)
      | u1_struct_0(sK5(sK2,X0)) = X0
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK5(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK3
      | ~ v4_tex_2(X2,sK2)
      | ~ m1_pre_topc(X2,sK2)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK3
        | ~ v4_tex_2(X2,sK2)
        | ~ m1_pre_topc(X2,sK2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,sK2)
              | ~ m1_pre_topc(X2,sK2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ v4_tex_2(X2,sK2)
            | ~ m1_pre_topc(X2,sK2)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v3_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK3
          | ~ v4_tex_2(X2,sK2)
          | ~ m1_pre_topc(X2,sK2)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v3_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f92,plain,(
    v1_pre_topc(sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f36,f63,f89])).

fof(f89,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_pre_topc(sK5(sK2,sK3)) ),
    inference(resolution,[],[f88,f37])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X0,sK2)
      | v1_xboole_0(X0)
      | v1_pre_topc(sK5(sK2,X0)) ) ),
    inference(global_subsumption,[],[f35,f33,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK2)
      | v1_pre_topc(sK5(sK2,X0))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f50,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(sK5(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,
    ( v4_tex_2(sK5(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2) ),
    inference(global_subsumption,[],[f38,f121])).

fof(f121,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v4_tex_2(sK5(sK2,sK3),sK2) ),
    inference(superposition,[],[f71,f117])).

fof(f117,plain,(
    sK3 = sK6(sK2,sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f63,f116])).

fof(f116,plain,
    ( sK3 = sK6(sK2,sK5(sK2,sK3))
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f115,f49])).

fof(f115,plain,
    ( v2_struct_0(sK5(sK2,sK3))
    | sK3 = sK6(sK2,sK5(sK2,sK3)) ),
    inference(global_subsumption,[],[f37,f36,f63,f114])).

fof(f114,plain,
    ( sK3 = sK6(sK2,sK5(sK2,sK3))
    | v2_struct_0(sK5(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f113,f95])).

fof(f113,plain,
    ( ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | sK3 = sK6(sK2,sK5(sK2,sK3))
    | v2_struct_0(sK5(sK2,sK3)) ),
    inference(forward_demodulation,[],[f112,f101])).

fof(f112,plain,
    ( ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v2_struct_0(sK5(sK2,sK3))
    | u1_struct_0(sK5(sK2,sK3)) = sK6(sK2,sK5(sK2,sK3)) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | v2_struct_0(sK5(sK2,sK3))
    | ~ m1_pre_topc(sK5(sK2,sK3),sK2)
    | u1_struct_0(sK5(sK2,sK3)) = sK6(sK2,sK5(sK2,sK3)) ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v4_tex_2(X0,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | u1_struct_0(X0) = sK6(sK2,X0) ) ),
    inference(global_subsumption,[],[f33,f72])).

fof(f72,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = sK6(sK2,X0)
      | ~ m1_pre_topc(X0,sK2)
      | v4_tex_2(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK6(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v4_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK6(X0,X1),X0)
                & u1_struct_0(X1) = sK6(X0,X1)
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK6(X0,X1),X0)
        & u1_struct_0(X1) = sK6(X0,X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f71,plain,(
    ! [X0] :
      ( ~ v3_tex_2(sK6(sK2,X0),sK2)
      | ~ m1_pre_topc(X0,sK2)
      | v4_tex_2(X0,sK2) ) ),
    inference(global_subsumption,[],[f33,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v3_tex_2(sK6(sK2,X0),sK2)
      | ~ m1_pre_topc(X0,sK2)
      | v4_tex_2(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tex_2(sK6(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v4_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f62,plain,(
    sP0(sK3,sK2) ),
    inference(global_subsumption,[],[f38,f61])).

fof(f61,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f59,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:14:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (3345)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.45  % (3337)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.46  % (3337)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f129,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f63,f128])).
% 0.19/0.46  fof(f128,plain,(
% 0.19/0.46    ~v2_tex_2(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.19/0.46    inference(resolution,[],[f127,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v2_struct_0(sK5(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((u1_struct_0(sK5(X0,X1)) = X1 & m1_pre_topc(sK5(X0,X1),X0) & v1_pre_topc(sK5(X0,X1)) & ~v2_struct_0(sK5(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK5(X0,X1)) = X1 & m1_pre_topc(sK5(X0,X1),X0) & v1_pre_topc(sK5(X0,X1)) & ~v2_struct_0(sK5(X0,X1))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,plain,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.19/0.46    inference(pure_predicate_removal,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.19/0.46  fof(f127,plain,(
% 0.19/0.46    v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f37,f36,f63,f126])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    v2_struct_0(sK5(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(sK3) | ~v2_tex_2(sK3,sK2)),
% 0.19/0.46    inference(resolution,[],[f125,f95])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    ( ! [X0] : (m1_pre_topc(sK5(sK2,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~v2_tex_2(X0,sK2)) )),
% 0.19/0.46    inference(global_subsumption,[],[f35,f33,f94])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~l1_pre_topc(sK2) | m1_pre_topc(sK5(sK2,X0),sK2) | v2_struct_0(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f51,f34])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(sK5(X0,X1),X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f125,plain,(
% 0.19/0.46    ~m1_pre_topc(sK5(sK2,sK3),sK2) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f124])).
% 0.19/0.46  fof(f124,plain,(
% 0.19/0.46    ~m1_pre_topc(sK5(sK2,sK3),sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(resolution,[],[f123,f110])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    ~v4_tex_2(sK5(sK2,sK3),sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f92,f109])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    ~v4_tex_2(sK5(sK2,sK3),sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | ~v1_pre_topc(sK5(sK2,sK3)) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f108])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    sK3 != sK3 | ~v4_tex_2(sK5(sK2,sK3),sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | ~v1_pre_topc(sK5(sK2,sK3)) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(superposition,[],[f39,f101])).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    sK3 = u1_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f36,f63,f98])).
% 0.19/0.46  fof(f98,plain,(
% 0.19/0.46    ~v2_tex_2(sK3,sK2) | v1_xboole_0(sK3) | sK3 = u1_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(resolution,[],[f97,f37])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X0,sK2) | v1_xboole_0(X0) | u1_struct_0(sK5(sK2,X0)) = X0) )),
% 0.19/0.46    inference(global_subsumption,[],[f35,f33,f96])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~l1_pre_topc(sK2) | u1_struct_0(sK5(sK2,X0)) = X0 | v2_struct_0(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f52,f34])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(sK5(X0,X1)) = X1 | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X2] : (u1_struct_0(X2) != sK3 | ~v4_tex_2(X2,sK2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    (! [X2] : (u1_struct_0(X2) != sK3 | ~v4_tex_2(X2,sK2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f8,f19,f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) => (! [X2] : (u1_struct_0(X2) != sK3 | ~v4_tex_2(X2,sK2) | ~m1_pre_topc(X2,sK2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f7])).
% 0.19/0.46  fof(f7,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,negated_conjecture,(
% 0.19/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.19/0.46    inference(negated_conjecture,[],[f4])).
% 0.19/0.46  fof(f4,conjecture,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).
% 0.19/0.46  fof(f92,plain,(
% 0.19/0.46    v1_pre_topc(sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f36,f63,f89])).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    ~v2_tex_2(sK3,sK2) | v1_xboole_0(sK3) | v1_pre_topc(sK5(sK2,sK3))),
% 0.19/0.46    inference(resolution,[],[f88,f37])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X0,sK2) | v1_xboole_0(X0) | v1_pre_topc(sK5(sK2,X0))) )),
% 0.19/0.46    inference(global_subsumption,[],[f35,f33,f87])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    ( ! [X0] : (~v2_tex_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X0) | ~l1_pre_topc(sK2) | v1_pre_topc(sK5(sK2,X0)) | v2_struct_0(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f50,f34])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v1_pre_topc(sK5(X0,X1)) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f123,plain,(
% 0.19/0.46    v4_tex_2(sK5(sK2,sK3),sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2)),
% 0.19/0.46    inference(global_subsumption,[],[f38,f121])).
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    ~v3_tex_2(sK3,sK2) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | v4_tex_2(sK5(sK2,sK3),sK2)),
% 0.19/0.46    inference(superposition,[],[f71,f117])).
% 0.19/0.46  fof(f117,plain,(
% 0.19/0.46    sK3 = sK6(sK2,sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f37,f36,f35,f34,f33,f63,f116])).
% 0.19/0.46  fof(f116,plain,(
% 0.19/0.46    sK3 = sK6(sK2,sK5(sK2,sK3)) | ~v2_tex_2(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.19/0.46    inference(resolution,[],[f115,f49])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    v2_struct_0(sK5(sK2,sK3)) | sK3 = sK6(sK2,sK5(sK2,sK3))),
% 0.19/0.46    inference(global_subsumption,[],[f37,f36,f63,f114])).
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    sK3 = sK6(sK2,sK5(sK2,sK3)) | v2_struct_0(sK5(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(sK3) | ~v2_tex_2(sK3,sK2)),
% 0.19/0.46    inference(resolution,[],[f113,f95])).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    ~m1_pre_topc(sK5(sK2,sK3),sK2) | sK3 = sK6(sK2,sK5(sK2,sK3)) | v2_struct_0(sK5(sK2,sK3))),
% 0.19/0.46    inference(forward_demodulation,[],[f112,f101])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    ~m1_pre_topc(sK5(sK2,sK3),sK2) | v2_struct_0(sK5(sK2,sK3)) | u1_struct_0(sK5(sK2,sK3)) = sK6(sK2,sK5(sK2,sK3))),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f111])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    ~m1_pre_topc(sK5(sK2,sK3),sK2) | v2_struct_0(sK5(sK2,sK3)) | ~m1_pre_topc(sK5(sK2,sK3),sK2) | u1_struct_0(sK5(sK2,sK3)) = sK6(sK2,sK5(sK2,sK3))),
% 0.19/0.46    inference(resolution,[],[f110,f73])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ( ! [X0] : (v4_tex_2(X0,sK2) | ~m1_pre_topc(X0,sK2) | u1_struct_0(X0) = sK6(sK2,X0)) )),
% 0.19/0.46    inference(global_subsumption,[],[f33,f72])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X0] : (u1_struct_0(X0) = sK6(sK2,X0) | ~m1_pre_topc(X0,sK2) | v4_tex_2(X0,sK2) | v2_struct_0(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f55,f35])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = sK6(X0,X1) | ~m1_pre_topc(X1,X0) | v4_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK6(X0,X1),X0) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK6(X0,X1),X0) & u1_struct_0(X1) = sK6(X0,X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(rectify,[],[f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X0] : (~v3_tex_2(sK6(sK2,X0),sK2) | ~m1_pre_topc(X0,sK2) | v4_tex_2(X0,sK2)) )),
% 0.19/0.46    inference(global_subsumption,[],[f33,f70])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0] : (~v3_tex_2(sK6(sK2,X0),sK2) | ~m1_pre_topc(X0,sK2) | v4_tex_2(X0,sK2) | v2_struct_0(sK2)) )),
% 0.19/0.46    inference(resolution,[],[f56,f35])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tex_2(sK6(X0,X1),X0) | ~m1_pre_topc(X1,X0) | v4_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f32])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    v3_tex_2(sK3,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    v2_tex_2(sK3,sK2)),
% 0.19/0.46    inference(resolution,[],[f62,f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~sP0(X0,X1) | v2_tex_2(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.19/0.46    inference(rectify,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.19/0.46    inference(flattening,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.19/0.46    inference(nnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    sP0(sK3,sK2)),
% 0.19/0.46    inference(global_subsumption,[],[f38,f61])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ~v3_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 0.19/0.46    inference(resolution,[],[f59,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.19/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    sP1(sK2,sK3)),
% 0.19/0.46    inference(resolution,[],[f58,f37])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.19/0.46    inference(resolution,[],[f48,f35])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.46    inference(definition_folding,[],[f10,f16,f15])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.46    inference(flattening,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ~v2_struct_0(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    v2_pre_topc(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    l1_pre_topc(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ~v1_xboole_0(sK3)),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (3337)------------------------------
% 0.19/0.47  % (3337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (3337)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (3337)Memory used [KB]: 6268
% 0.19/0.47  % (3337)Time elapsed: 0.062 s
% 0.19/0.47  % (3337)------------------------------
% 0.19/0.47  % (3337)------------------------------
% 0.19/0.47  % (3324)Success in time 0.118 s
%------------------------------------------------------------------------------

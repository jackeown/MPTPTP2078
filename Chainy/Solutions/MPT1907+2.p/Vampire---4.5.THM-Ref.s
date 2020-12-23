%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1907+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 4.17s
% Output     : Refutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 459 expanded)
%              Number of leaves         :    7 ( 135 expanded)
%              Depth                    :   21
%              Number of atoms          :  530 (3388 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14295,f5435])).

fof(f5435,plain,(
    ~ r1_borsuk_1(sK2,sK3) ),
    inference(literal_reordering,[],[f4598])).

fof(f4598,plain,(
    ~ r1_borsuk_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f4279])).

fof(f4279,plain,
    ( ~ r1_borsuk_1(sK2,sK3)
    & m1_pre_topc(sK3,sK2)
    & v4_tex_2(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3782,f4278,f4277])).

fof(f4277,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK2,X1)
          & m1_pre_topc(X1,sK2)
          & v4_tex_2(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f4278,plain,
    ( ? [X1] :
        ( ~ r1_borsuk_1(sK2,X1)
        & m1_pre_topc(X1,sK2)
        & v4_tex_2(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_borsuk_1(sK2,sK3)
      & m1_pre_topc(sK3,sK2)
      & v4_tex_2(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3782,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3781])).

fof(f3781,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3766])).

fof(f3766,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3765])).

fof(f3765,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tex_2)).

fof(f14295,plain,(
    r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14294,f5438])).

fof(f5438,plain,(
    ~ v2_struct_0(sK3) ),
    inference(literal_reordering,[],[f4595])).

fof(f4595,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f4279])).

fof(f14294,plain,
    ( v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14293,f5436])).

fof(f5436,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(literal_reordering,[],[f4597])).

fof(f4597,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f14293,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14292,f7429])).

fof(f7429,plain,(
    v1_funct_1(sK22(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f7428,f5442])).

fof(f5442,plain,(
    ~ v2_struct_0(sK2) ),
    inference(literal_reordering,[],[f4591])).

fof(f4591,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f7428,plain,
    ( v1_funct_1(sK22(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7427,f5441])).

fof(f5441,plain,(
    v2_pre_topc(sK2) ),
    inference(literal_reordering,[],[f4592])).

fof(f4592,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f7427,plain,
    ( v1_funct_1(sK22(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7426,f5440])).

fof(f5440,plain,(
    v3_tdlat_3(sK2) ),
    inference(literal_reordering,[],[f4593])).

fof(f4593,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f7426,plain,
    ( v1_funct_1(sK22(sK2,sK3))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7425,f5439])).

fof(f5439,plain,(
    l1_pre_topc(sK2) ),
    inference(literal_reordering,[],[f4594])).

fof(f4594,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f7425,plain,
    ( v1_funct_1(sK22(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7424,f5438])).

fof(f7424,plain,
    ( v1_funct_1(sK22(sK2,sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7419,f5436])).

fof(f7419,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v1_funct_1(sK22(sK2,sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f5437,f5578])).

fof(f5578,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(sK22(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4730])).

fof(f4730,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK22(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4329])).

fof(f4329,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK22(X0,X1),X0,X1)
            & m1_subset_1(sK22(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK22(X0,X1),X0,X1)
            & v1_funct_2(sK22(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK22(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f3878,f4328])).

fof(f4328,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( v3_borsuk_1(sK22(X0,X1),X0,X1)
        & m1_subset_1(sK22(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK22(X0,X1),X0,X1)
        & v1_funct_2(sK22(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK22(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3878,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3877])).

fof(f3877,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3764])).

fof(f3764,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tex_2)).

fof(f5437,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(literal_reordering,[],[f4596])).

fof(f4596,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f4279])).

fof(f14292,plain,
    ( ~ v1_funct_1(sK22(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14291,f7453])).

fof(f7453,plain,(
    v3_borsuk_1(sK22(sK2,sK3),sK2,sK3) ),
    inference(subsumption_resolution,[],[f7452,f5442])).

fof(f7452,plain,
    ( v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7451,f5441])).

fof(f7451,plain,
    ( v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7450,f5440])).

fof(f7450,plain,
    ( v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7449,f5439])).

fof(f7449,plain,
    ( v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7448,f5438])).

fof(f7448,plain,
    ( v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7423,f5436])).

fof(f7423,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f5437,f5574])).

fof(f5574,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_borsuk_1(sK22(X0,X1),X0,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4734])).

fof(f4734,plain,(
    ! [X0,X1] :
      ( v3_borsuk_1(sK22(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4329])).

fof(f14291,plain,
    ( ~ v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ v1_funct_1(sK22(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14290,f7441])).

fof(f7441,plain,(
    v5_pre_topc(sK22(sK2,sK3),sK2,sK3) ),
    inference(subsumption_resolution,[],[f7440,f5442])).

fof(f7440,plain,
    ( v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7439,f5441])).

fof(f7439,plain,
    ( v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7438,f5440])).

fof(f7438,plain,
    ( v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7437,f5439])).

fof(f7437,plain,
    ( v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7436,f5438])).

fof(f7436,plain,
    ( v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7421,f5436])).

fof(f7421,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f5437,f5576])).

fof(f5576,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v5_pre_topc(sK22(X0,X1),X0,X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4732])).

fof(f4732,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK22(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4329])).

fof(f14290,plain,
    ( ~ v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | ~ v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ v1_funct_1(sK22(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f14289,f7447])).

fof(f7447,plain,(
    m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f7446,f5442])).

fof(f7446,plain,
    ( m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7445,f5441])).

fof(f7445,plain,
    ( m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7444,f5440])).

fof(f7444,plain,
    ( m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7443,f5439])).

fof(f7443,plain,
    ( m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7442,f5438])).

fof(f7442,plain,
    ( m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7422,f5436])).

fof(f7422,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f5437,f5575])).

fof(f5575,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK22(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4733])).

fof(f4733,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK22(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4329])).

fof(f14289,plain,
    ( ~ m1_subset_1(sK22(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK22(sK2,sK3),sK2,sK3)
    | ~ v3_borsuk_1(sK22(sK2,sK3),sK2,sK3)
    | ~ v1_funct_1(sK22(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(resolution,[],[f14288,f7435])).

fof(f7435,plain,(
    v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f7434,f5442])).

fof(f7434,plain,
    ( v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7433,f5441])).

fof(f7433,plain,
    ( v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7432,f5440])).

fof(f7432,plain,
    ( v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7431,f5439])).

fof(f7431,plain,
    ( v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7430,f5438])).

fof(f7430,plain,
    ( v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f7420,f5436])).

fof(f7420,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v1_funct_2(sK22(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f5437,f5577])).

fof(f5577,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_2(sK22(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4731])).

fof(f4731,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK22(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4329])).

fof(f14288,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK2,X1)
      | ~ v3_borsuk_1(X0,sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | r1_borsuk_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f7226,f5442])).

fof(f7226,plain,(
    ! [X0,X1] :
      ( ~ v3_borsuk_1(X0,sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK2,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | r1_borsuk_1(sK2,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f7161,f5439])).

fof(f7161,plain,(
    ! [X0,X1] :
      ( ~ v3_borsuk_1(X0,sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK2,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK2)
      | r1_borsuk_1(sK2,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f5441,f5443])).

fof(f5443,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_borsuk_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4604])).

fof(f4604,plain,(
    ! [X2,X0,X1] :
      ( r1_borsuk_1(X0,X1)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4283])).

fof(f4283,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ( v3_borsuk_1(sK4(X0,X1),X0,X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(sK4(X0,X1),X0,X1)
                & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(sK4(X0,X1)) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4281,f4282])).

fof(f4282,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( v3_borsuk_1(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X3,X0,X1)
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( v3_borsuk_1(sK4(X0,X1),X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK4(X0,X1),X0,X1)
        & v1_funct_2(sK4(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4281,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ? [X3] :
                  ( v3_borsuk_1(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X3,X0,X1)
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4280])).

fof(f4280,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ? [X2] :
                  ( v3_borsuk_1(X2,X0,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3784])).

fof(f3784,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3783])).

fof(f3783,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3616])).

fof(f3616,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( r1_borsuk_1(X0,X1)
          <=> ? [X2] :
                ( v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_borsuk_1)).
%------------------------------------------------------------------------------

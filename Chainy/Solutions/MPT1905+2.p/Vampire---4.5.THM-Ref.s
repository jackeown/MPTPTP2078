%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1905+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 10.12s
% Output     : Refutation 10.12s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 409 expanded)
%              Number of leaves         :    7 ( 120 expanded)
%              Depth                    :   20
%              Number of atoms          :  470 (2669 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9359,f7645])).

fof(f7645,plain,(
    m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f7639,f4624])).

fof(f4624,plain,(
    ~ v2_struct_0(sK3) ),
    inference(literal_reordering,[],[f4188])).

fof(f4188,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f4016])).

fof(f4016,plain,
    ( ~ r1_borsuk_1(sK2,sK3)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3771,f4015,f4014])).

fof(f4014,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK2,X1)
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f4015,plain,
    ( ? [X1] :
        ( ~ r1_borsuk_1(sK2,X1)
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_borsuk_1(sK2,sK3)
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3771,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3770])).

fof(f3770,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3763])).

fof(f3763,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3762])).

fof(f3762,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tex_2)).

fof(f7639,plain,
    ( v2_struct_0(sK3)
    | m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(resolution,[],[f7636,f4623])).

fof(f4623,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(literal_reordering,[],[f4189])).

fof(f4189,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f4016])).

fof(f7636,plain,(
    ! [X30] :
      ( ~ m1_pre_topc(X30,sK2)
      | v2_struct_0(X30)
      | m1_subset_1(sK15(sK2,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X30)))) ) ),
    inference(subsumption_resolution,[],[f5896,f4628])).

fof(f4628,plain,(
    ~ v2_struct_0(sK2) ),
    inference(literal_reordering,[],[f4184])).

fof(f4184,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4016])).

fof(f5896,plain,(
    ! [X30] :
      ( ~ m1_pre_topc(X30,sK2)
      | v2_struct_0(X30)
      | m1_subset_1(sK15(sK2,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X30))))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5895,f4626])).

fof(f4626,plain,(
    v1_tdlat_3(sK2) ),
    inference(literal_reordering,[],[f4186])).

fof(f4186,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f4016])).

fof(f5895,plain,(
    ! [X30] :
      ( ~ m1_pre_topc(X30,sK2)
      | v2_struct_0(X30)
      | ~ v1_tdlat_3(sK2)
      | m1_subset_1(sK15(sK2,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X30))))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5802,f4625])).

fof(f4625,plain,(
    l1_pre_topc(sK2) ),
    inference(literal_reordering,[],[f4187])).

fof(f4187,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4016])).

fof(f5802,plain,(
    ! [X30] :
      ( ~ m1_pre_topc(X30,sK2)
      | v2_struct_0(X30)
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | m1_subset_1(sK15(sK2,X30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X30))))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4627,f4686])).

fof(f4686,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4250])).

fof(f4250,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f4047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK15(X0,X1),X0,X1)
            & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK15(X0,X1),X0,X1)
            & v1_funct_2(sK15(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK15(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f3823,f4046])).

fof(f4046,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( v3_borsuk_1(sK15(X0,X1),X0,X1)
        & m1_subset_1(sK15(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK15(X0,X1),X0,X1)
        & v1_funct_2(sK15(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK15(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3823,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3822])).

fof(f3822,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3761])).

fof(f3761,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tex_2)).

fof(f4627,plain,(
    v2_pre_topc(sK2) ),
    inference(literal_reordering,[],[f4185])).

fof(f4185,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4016])).

fof(f9359,plain,(
    ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f9358,f4622])).

fof(f4622,plain,(
    ~ r1_borsuk_1(sK2,sK3) ),
    inference(literal_reordering,[],[f4190])).

fof(f4190,plain,(
    ~ r1_borsuk_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f4016])).

fof(f9358,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f9357,f4624])).

fof(f9357,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f9356,f4623])).

fof(f9356,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f9355,f7544])).

fof(f7544,plain,(
    v1_funct_1(sK15(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f7538,f4624])).

fof(f7538,plain,
    ( v2_struct_0(sK3)
    | v1_funct_1(sK15(sK2,sK3)) ),
    inference(resolution,[],[f7535,f4623])).

fof(f7535,plain,(
    ! [X33] :
      ( ~ m1_pre_topc(X33,sK2)
      | v2_struct_0(X33)
      | v1_funct_1(sK15(sK2,X33)) ) ),
    inference(subsumption_resolution,[],[f5902,f4628])).

fof(f5902,plain,(
    ! [X33] :
      ( ~ m1_pre_topc(X33,sK2)
      | v2_struct_0(X33)
      | v1_funct_1(sK15(sK2,X33))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5901,f4626])).

fof(f5901,plain,(
    ! [X33] :
      ( ~ m1_pre_topc(X33,sK2)
      | v2_struct_0(X33)
      | ~ v1_tdlat_3(sK2)
      | v1_funct_1(sK15(sK2,X33))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5805,f4625])).

fof(f5805,plain,(
    ! [X33] :
      ( ~ m1_pre_topc(X33,sK2)
      | v2_struct_0(X33)
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v1_funct_1(sK15(sK2,X33))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4627,f4689])).

fof(f4689,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v1_funct_1(sK15(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4247])).

fof(f4247,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK15(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f9355,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK15(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f9354,f7561])).

fof(f7561,plain,(
    v3_borsuk_1(sK15(sK2,sK3),sK2,sK3) ),
    inference(subsumption_resolution,[],[f7555,f4624])).

fof(f7555,plain,
    ( v2_struct_0(sK3)
    | v3_borsuk_1(sK15(sK2,sK3),sK2,sK3) ),
    inference(resolution,[],[f7552,f4623])).

fof(f7552,plain,(
    ! [X29] :
      ( ~ m1_pre_topc(X29,sK2)
      | v2_struct_0(X29)
      | v3_borsuk_1(sK15(sK2,X29),sK2,X29) ) ),
    inference(subsumption_resolution,[],[f5894,f4628])).

fof(f5894,plain,(
    ! [X29] :
      ( ~ m1_pre_topc(X29,sK2)
      | v2_struct_0(X29)
      | v3_borsuk_1(sK15(sK2,X29),sK2,X29)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5893,f4626])).

fof(f5893,plain,(
    ! [X29] :
      ( ~ m1_pre_topc(X29,sK2)
      | v2_struct_0(X29)
      | ~ v1_tdlat_3(sK2)
      | v3_borsuk_1(sK15(sK2,X29),sK2,X29)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5801,f4625])).

fof(f5801,plain,(
    ! [X29] :
      ( ~ m1_pre_topc(X29,sK2)
      | v2_struct_0(X29)
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v3_borsuk_1(sK15(sK2,X29),sK2,X29)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4627,f4685])).

fof(f4685,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v3_borsuk_1(sK15(X0,X1),X0,X1)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4251])).

fof(f4251,plain,(
    ! [X0,X1] :
      ( v3_borsuk_1(sK15(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f9354,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v3_borsuk_1(sK15(sK2,sK3),sK2,sK3)
    | ~ v1_funct_1(sK15(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f9346,f7600])).

fof(f7600,plain,(
    v5_pre_topc(sK15(sK2,sK3),sK2,sK3) ),
    inference(subsumption_resolution,[],[f7594,f4624])).

fof(f7594,plain,
    ( v2_struct_0(sK3)
    | v5_pre_topc(sK15(sK2,sK3),sK2,sK3) ),
    inference(resolution,[],[f7562,f4623])).

fof(f7562,plain,(
    ! [X31] :
      ( ~ m1_pre_topc(X31,sK2)
      | v2_struct_0(X31)
      | v5_pre_topc(sK15(sK2,X31),sK2,X31) ) ),
    inference(subsumption_resolution,[],[f5898,f4628])).

fof(f5898,plain,(
    ! [X31] :
      ( ~ m1_pre_topc(X31,sK2)
      | v2_struct_0(X31)
      | v5_pre_topc(sK15(sK2,X31),sK2,X31)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5897,f4626])).

fof(f5897,plain,(
    ! [X31] :
      ( ~ m1_pre_topc(X31,sK2)
      | v2_struct_0(X31)
      | ~ v1_tdlat_3(sK2)
      | v5_pre_topc(sK15(sK2,X31),sK2,X31)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5803,f4625])).

fof(f5803,plain,(
    ! [X31] :
      ( ~ m1_pre_topc(X31,sK2)
      | v2_struct_0(X31)
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v5_pre_topc(sK15(sK2,X31),sK2,X31)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4627,f4687])).

fof(f4687,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v5_pre_topc(sK15(X0,X1),X0,X1)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4249])).

fof(f4249,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK15(X0,X1),X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4047])).

fof(f9346,plain,
    ( ~ m1_subset_1(sK15(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK15(sK2,sK3),sK2,sK3)
    | ~ v3_borsuk_1(sK15(sK2,sK3),sK2,sK3)
    | ~ v1_funct_1(sK15(sK2,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | r1_borsuk_1(sK2,sK3) ),
    inference(resolution,[],[f7631,f8037])).

fof(f8037,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK2,X1)
      | ~ v3_borsuk_1(X0,sK2,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | r1_borsuk_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f5873,f4628])).

fof(f5873,plain,(
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
    inference(subsumption_resolution,[],[f5783,f4625])).

fof(f5783,plain,(
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
    inference(resolution,[],[f4627,f4629])).

fof(f4629,plain,(
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
    inference(literal_reordering,[],[f4196])).

fof(f4196,plain,(
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
    inference(cnf_transformation,[],[f4020])).

fof(f4020,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4018,f4019])).

fof(f4019,plain,(
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

fof(f4018,plain,(
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
    inference(rectify,[],[f4017])).

fof(f4017,plain,(
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
    inference(nnf_transformation,[],[f3773])).

fof(f3773,plain,(
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
    inference(flattening,[],[f3772])).

fof(f3772,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_borsuk_1)).

fof(f7631,plain,(
    v1_funct_2(sK15(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f7625,f4624])).

fof(f7625,plain,
    ( v2_struct_0(sK3)
    | v1_funct_2(sK15(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f7622,f4623])).

fof(f7622,plain,(
    ! [X32] :
      ( ~ m1_pre_topc(X32,sK2)
      | v2_struct_0(X32)
      | v1_funct_2(sK15(sK2,X32),u1_struct_0(sK2),u1_struct_0(X32)) ) ),
    inference(subsumption_resolution,[],[f5900,f4628])).

fof(f5900,plain,(
    ! [X32] :
      ( ~ m1_pre_topc(X32,sK2)
      | v2_struct_0(X32)
      | v1_funct_2(sK15(sK2,X32),u1_struct_0(sK2),u1_struct_0(X32))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5899,f4626])).

fof(f5899,plain,(
    ! [X32] :
      ( ~ m1_pre_topc(X32,sK2)
      | v2_struct_0(X32)
      | ~ v1_tdlat_3(sK2)
      | v1_funct_2(sK15(sK2,X32),u1_struct_0(sK2),u1_struct_0(X32))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5804,f4625])).

fof(f5804,plain,(
    ! [X32] :
      ( ~ m1_pre_topc(X32,sK2)
      | v2_struct_0(X32)
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v1_funct_2(sK15(sK2,X32),u1_struct_0(sK2),u1_struct_0(X32))
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4627,f4688])).

fof(f4688,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v1_funct_2(sK15(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4248])).

fof(f4248,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK15(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4047])).
%------------------------------------------------------------------------------

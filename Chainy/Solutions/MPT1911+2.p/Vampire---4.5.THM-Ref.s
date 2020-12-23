%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1911+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 10.73s
% Output     : Refutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 412 expanded)
%              Number of leaves         :    7 ( 135 expanded)
%              Depth                    :   23
%              Number of atoms          :  471 (3296 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33460,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33459,f6659])).

fof(f6659,plain,(
    ~ v2_struct_0(sK76) ),
    inference(cnf_transformation,[],[f5474])).

fof(f5474,plain,
    ( ~ r1_borsuk_1(sK76,sK77)
    & m1_pre_topc(sK77,sK76)
    & v1_tdlat_3(sK77)
    & ~ v2_struct_0(sK77)
    & l1_pre_topc(sK76)
    & v3_tdlat_3(sK76)
    & v2_pre_topc(sK76)
    & ~ v2_struct_0(sK76) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK76,sK77])],[f3828,f5473,f5472])).

fof(f5472,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_borsuk_1(X0,X1)
            & m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_borsuk_1(sK76,X1)
          & m1_pre_topc(X1,sK76)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK76)
      & v3_tdlat_3(sK76)
      & v2_pre_topc(sK76)
      & ~ v2_struct_0(sK76) ) ),
    introduced(choice_axiom,[])).

fof(f5473,plain,
    ( ? [X1] :
        ( ~ r1_borsuk_1(sK76,X1)
        & m1_pre_topc(X1,sK76)
        & v1_tdlat_3(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_borsuk_1(sK76,sK77)
      & m1_pre_topc(sK77,sK76)
      & v1_tdlat_3(sK77)
      & ~ v2_struct_0(sK77) ) ),
    introduced(choice_axiom,[])).

fof(f3828,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3827])).

fof(f3827,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_borsuk_1(X0,X1)
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3772])).

fof(f3772,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => r1_borsuk_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f3771])).

fof(f3771,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => r1_borsuk_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tex_2)).

fof(f33459,plain,(
    v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33458,f6660])).

fof(f6660,plain,(
    v2_pre_topc(sK76) ),
    inference(cnf_transformation,[],[f5474])).

fof(f33458,plain,
    ( ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33457,f6662])).

fof(f6662,plain,(
    l1_pre_topc(sK76) ),
    inference(cnf_transformation,[],[f5474])).

fof(f33457,plain,
    ( ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33456,f6663])).

fof(f6663,plain,(
    ~ v2_struct_0(sK77) ),
    inference(cnf_transformation,[],[f5474])).

fof(f33456,plain,
    ( v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33455,f6665])).

fof(f6665,plain,(
    m1_pre_topc(sK77,sK76) ),
    inference(cnf_transformation,[],[f5474])).

fof(f33455,plain,
    ( ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33454,f9937])).

fof(f9937,plain,(
    v1_funct_1(sK148(sK76,sK77)) ),
    inference(subsumption_resolution,[],[f9936,f6659])).

fof(f9936,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9935,f6660])).

fof(f9935,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9934,f6661])).

fof(f6661,plain,(
    v3_tdlat_3(sK76) ),
    inference(cnf_transformation,[],[f5474])).

fof(f9934,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9933,f6662])).

fof(f9933,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9932,f6663])).

fof(f9932,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9796,f6664])).

fof(f6664,plain,(
    v1_tdlat_3(sK77) ),
    inference(cnf_transformation,[],[f5474])).

fof(f9796,plain,
    ( v1_funct_1(sK148(sK76,sK77))
    | ~ v1_tdlat_3(sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f6665,f7081])).

fof(f7081,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(sK148(X0,X1))
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5662])).

fof(f5662,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_borsuk_1(sK148(X0,X1),X0,X1)
            & m1_subset_1(sK148(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(sK148(X0,X1),X0,X1)
            & v1_funct_2(sK148(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(sK148(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK148])],[f4072,f5661])).

fof(f5661,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( v3_borsuk_1(sK148(X0,X1),X0,X1)
        & m1_subset_1(sK148(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK148(X0,X1),X0,X1)
        & v1_funct_2(sK148(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK148(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4072,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4071])).

fof(f4071,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3770])).

fof(f3770,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tex_2)).

fof(f33454,plain,
    ( ~ v1_funct_1(sK148(sK76,sK77))
    | ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33453,f9943])).

fof(f9943,plain,(
    v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77)) ),
    inference(subsumption_resolution,[],[f9942,f6659])).

fof(f9942,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9941,f6660])).

fof(f9941,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9940,f6661])).

fof(f9940,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9939,f6662])).

fof(f9939,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9938,f6663])).

fof(f9938,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9797,f6664])).

fof(f9797,plain,
    ( v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v1_tdlat_3(sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f6665,f7082])).

fof(f7082,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(sK148(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5662])).

fof(f33453,plain,
    ( ~ v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v1_funct_1(sK148(sK76,sK77))
    | ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33452,f9949])).

fof(f9949,plain,(
    v5_pre_topc(sK148(sK76,sK77),sK76,sK77) ),
    inference(subsumption_resolution,[],[f9948,f6659])).

fof(f9948,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9947,f6660])).

fof(f9947,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9946,f6661])).

fof(f9946,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9945,f6662])).

fof(f9945,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9944,f6663])).

fof(f9944,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9798,f6664])).

fof(f9798,plain,
    ( v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v1_tdlat_3(sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f6665,f7083])).

fof(f7083,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v5_pre_topc(sK148(X0,X1),X0,X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5662])).

fof(f33452,plain,
    ( ~ v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v1_funct_1(sK148(sK76,sK77))
    | ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33451,f6666])).

fof(f6666,plain,(
    ~ r1_borsuk_1(sK76,sK77) ),
    inference(cnf_transformation,[],[f5474])).

fof(f33451,plain,
    ( r1_borsuk_1(sK76,sK77)
    | ~ v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v1_funct_1(sK148(sK76,sK77))
    | ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f33290,f9961])).

fof(f9961,plain,(
    v3_borsuk_1(sK148(sK76,sK77),sK76,sK77) ),
    inference(subsumption_resolution,[],[f9960,f6659])).

fof(f9960,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9959,f6660])).

fof(f9959,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9958,f6661])).

fof(f9958,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9957,f6662])).

fof(f9957,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9956,f6663])).

fof(f9956,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9800,f6664])).

fof(f9800,plain,
    ( v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | ~ v1_tdlat_3(sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f6665,f7085])).

fof(f7085,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v3_borsuk_1(sK148(X0,X1),X0,X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5662])).

fof(f33290,plain,
    ( ~ v3_borsuk_1(sK148(sK76,sK77),sK76,sK77)
    | r1_borsuk_1(sK76,sK77)
    | ~ v5_pre_topc(sK148(sK76,sK77),sK76,sK77)
    | ~ v1_funct_2(sK148(sK76,sK77),u1_struct_0(sK76),u1_struct_0(sK77))
    | ~ v1_funct_1(sK148(sK76,sK77))
    | ~ m1_pre_topc(sK77,sK76)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f9955,f6672])).

fof(f6672,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | r1_borsuk_1(X0,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5478])).

fof(f5478,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_borsuk_1(X0,X1)
              | ! [X2] :
                  ( ~ v3_borsuk_1(X2,X0,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(X2) ) )
            & ( ( v3_borsuk_1(sK78(X0,X1),X0,X1)
                & m1_subset_1(sK78(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(sK78(X0,X1),X0,X1)
                & v1_funct_2(sK78(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(sK78(X0,X1)) )
              | ~ r1_borsuk_1(X0,X1) ) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK78])],[f5476,f5477])).

fof(f5477,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( v3_borsuk_1(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X3,X0,X1)
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( v3_borsuk_1(sK78(X0,X1),X0,X1)
        & m1_subset_1(sK78(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK78(X0,X1),X0,X1)
        & v1_funct_2(sK78(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK78(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5476,plain,(
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
    inference(rectify,[],[f5475])).

fof(f5475,plain,(
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
    inference(nnf_transformation,[],[f3830])).

fof(f3830,plain,(
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
    inference(flattening,[],[f3829])).

fof(f3829,plain,(
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

fof(f9955,plain,(
    m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77)))) ),
    inference(subsumption_resolution,[],[f9954,f6659])).

fof(f9954,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9953,f6660])).

fof(f9953,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9952,f6661])).

fof(f9952,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9951,f6662])).

fof(f9951,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9950,f6663])).

fof(f9950,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(subsumption_resolution,[],[f9799,f6664])).

fof(f9799,plain,
    ( m1_subset_1(sK148(sK76,sK77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK76),u1_struct_0(sK77))))
    | ~ v1_tdlat_3(sK77)
    | v2_struct_0(sK77)
    | ~ l1_pre_topc(sK76)
    | ~ v3_tdlat_3(sK76)
    | ~ v2_pre_topc(sK76)
    | v2_struct_0(sK76) ),
    inference(resolution,[],[f6665,f7084])).

fof(f7084,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK148(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5662])).
%------------------------------------------------------------------------------

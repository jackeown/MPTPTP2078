%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1866+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 15.11s
% Output     : Refutation 15.11s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 395 expanded)
%              Number of leaves         :    6 ( 128 expanded)
%              Depth                    :   22
%              Number of atoms          :  289 (4008 expanded)
%              Number of equality atoms :   28 ( 404 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22826,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22825,f6263])).

fof(f6263,plain,(
    ~ v2_struct_0(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f6262,f4462])).

fof(f4462,plain,(
    ~ v2_struct_0(sK32) ),
    inference(cnf_transformation,[],[f4136])).

fof(f4136,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK33
        | ~ m1_pre_topc(X2,sK32)
        | ~ v1_tdlat_3(X2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v2_tex_2(sK33,sK32)
    & m1_subset_1(sK33,k1_zfmisc_1(u1_struct_0(sK32)))
    & ~ v1_xboole_0(sK33)
    & l1_pre_topc(sK32)
    & v2_pre_topc(sK32)
    & ~ v2_struct_0(sK32) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32,sK33])],[f3694,f4135,f4134])).

fof(f4134,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_tdlat_3(X2)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,sK32)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,sK32)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK32)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK32)
      & v2_pre_topc(sK32)
      & ~ v2_struct_0(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f4135,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ m1_pre_topc(X2,sK32)
            | ~ v1_tdlat_3(X2)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v2_tex_2(X1,sK32)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK32)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK33
          | ~ m1_pre_topc(X2,sK32)
          | ~ v1_tdlat_3(X2)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v2_tex_2(sK33,sK32)
      & m1_subset_1(sK33,k1_zfmisc_1(u1_struct_0(sK32)))
      & ~ v1_xboole_0(sK33) ) ),
    introduced(choice_axiom,[])).

fof(f3694,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3693])).

fof(f3693,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3677])).

fof(f3677,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3676])).

fof(f3676,conjecture,(
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

fof(f6262,plain,
    ( ~ v2_struct_0(sK42(sK32,sK33))
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6261,f4464])).

fof(f4464,plain,(
    l1_pre_topc(sK32) ),
    inference(cnf_transformation,[],[f4136])).

fof(f6261,plain,
    ( ~ v2_struct_0(sK42(sK32,sK33))
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6075,f4465])).

fof(f4465,plain,(
    ~ v1_xboole_0(sK33) ),
    inference(cnf_transformation,[],[f4136])).

fof(f6075,plain,
    ( ~ v2_struct_0(sK42(sK32,sK33))
    | v1_xboole_0(sK33)
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(resolution,[],[f4466,f4509])).

fof(f4509,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK42(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4157])).

fof(f4157,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK42(X0,X1)) = X1
            & m1_pre_topc(sK42(X0,X1),X0)
            & v1_pre_topc(sK42(X0,X1))
            & ~ v2_struct_0(sK42(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK42])],[f3730,f4156])).

fof(f4156,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK42(X0,X1)) = X1
        & m1_pre_topc(sK42(X0,X1),X0)
        & v1_pre_topc(sK42(X0,X1))
        & ~ v2_struct_0(sK42(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3730,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3729])).

fof(f3729,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3651])).

fof(f3651,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f4466,plain,(
    m1_subset_1(sK33,k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(cnf_transformation,[],[f4136])).

fof(f22825,plain,(
    v2_struct_0(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f22824,f6266])).

fof(f6266,plain,(
    v1_pre_topc(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f6265,f4462])).

fof(f6265,plain,
    ( v1_pre_topc(sK42(sK32,sK33))
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6264,f4464])).

fof(f6264,plain,
    ( v1_pre_topc(sK42(sK32,sK33))
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6076,f4465])).

fof(f6076,plain,
    ( v1_pre_topc(sK42(sK32,sK33))
    | v1_xboole_0(sK33)
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(resolution,[],[f4466,f4510])).

fof(f4510,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK42(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4157])).

fof(f22824,plain,
    ( ~ v1_pre_topc(sK42(sK32,sK33))
    | v2_struct_0(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f22823,f6272])).

fof(f6272,plain,(
    sK33 = u1_struct_0(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f6271,f4462])).

fof(f6271,plain,
    ( sK33 = u1_struct_0(sK42(sK32,sK33))
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6270,f4464])).

fof(f6270,plain,
    ( sK33 = u1_struct_0(sK42(sK32,sK33))
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6078,f4465])).

fof(f6078,plain,
    ( sK33 = u1_struct_0(sK42(sK32,sK33))
    | v1_xboole_0(sK33)
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(resolution,[],[f4466,f4512])).

fof(f4512,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK42(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4157])).

fof(f22823,plain,
    ( sK33 != u1_struct_0(sK42(sK32,sK33))
    | ~ v1_pre_topc(sK42(sK32,sK33))
    | v2_struct_0(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f22814,f6269])).

fof(f6269,plain,(
    m1_pre_topc(sK42(sK32,sK33),sK32) ),
    inference(subsumption_resolution,[],[f6268,f4462])).

fof(f6268,plain,
    ( m1_pre_topc(sK42(sK32,sK33),sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6267,f4464])).

fof(f6267,plain,
    ( m1_pre_topc(sK42(sK32,sK33),sK32)
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f6077,f4465])).

fof(f6077,plain,
    ( m1_pre_topc(sK42(sK32,sK33),sK32)
    | v1_xboole_0(sK33)
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(resolution,[],[f4466,f4511])).

fof(f4511,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK42(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4157])).

fof(f22814,plain,
    ( ~ m1_pre_topc(sK42(sK32,sK33),sK32)
    | sK33 != u1_struct_0(sK42(sK32,sK33))
    | ~ v1_pre_topc(sK42(sK32,sK33))
    | v2_struct_0(sK42(sK32,sK33)) ),
    inference(resolution,[],[f16961,f4468])).

fof(f4468,plain,(
    ! [X2] :
      ( ~ v1_tdlat_3(X2)
      | ~ m1_pre_topc(X2,sK32)
      | u1_struct_0(X2) != sK33
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f4136])).

fof(f16961,plain,(
    v1_tdlat_3(sK42(sK32,sK33)) ),
    inference(subsumption_resolution,[],[f16960,f4466])).

fof(f16960,plain,
    ( ~ m1_subset_1(sK33,k1_zfmisc_1(u1_struct_0(sK32)))
    | v1_tdlat_3(sK42(sK32,sK33)) ),
    inference(forward_demodulation,[],[f16959,f6272])).

fof(f16959,plain,
    ( v1_tdlat_3(sK42(sK32,sK33))
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(subsumption_resolution,[],[f16958,f4467])).

fof(f4467,plain,(
    v2_tex_2(sK33,sK32) ),
    inference(cnf_transformation,[],[f4136])).

fof(f16958,plain,
    ( ~ v2_tex_2(sK33,sK32)
    | v1_tdlat_3(sK42(sK32,sK33))
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(forward_demodulation,[],[f16957,f6272])).

fof(f16957,plain,
    ( v1_tdlat_3(sK42(sK32,sK33))
    | ~ v2_tex_2(u1_struct_0(sK42(sK32,sK33)),sK32)
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(subsumption_resolution,[],[f16956,f4462])).

fof(f16956,plain,
    ( v1_tdlat_3(sK42(sK32,sK33))
    | ~ v2_tex_2(u1_struct_0(sK42(sK32,sK33)),sK32)
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32)))
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f16955,f4464])).

fof(f16955,plain,
    ( v1_tdlat_3(sK42(sK32,sK33))
    | ~ v2_tex_2(u1_struct_0(sK42(sK32,sK33)),sK32)
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(subsumption_resolution,[],[f16619,f6263])).

fof(f16619,plain,
    ( v1_tdlat_3(sK42(sK32,sK33))
    | ~ v2_tex_2(u1_struct_0(sK42(sK32,sK33)),sK32)
    | ~ m1_subset_1(u1_struct_0(sK42(sK32,sK33)),k1_zfmisc_1(u1_struct_0(sK32)))
    | v2_struct_0(sK42(sK32,sK33))
    | ~ l1_pre_topc(sK32)
    | v2_struct_0(sK32) ),
    inference(resolution,[],[f6269,f5123])).

fof(f5123,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4515])).

fof(f4515,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4160])).

fof(f4160,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3733])).

fof(f3733,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3732])).

fof(f3732,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3667])).

fof(f3667,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
%------------------------------------------------------------------------------

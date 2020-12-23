%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1856+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 254 expanded)
%              Number of leaves         :    8 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 (1443 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5329,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5216,f5142])).

fof(f5142,plain,(
    v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5141,f4417])).

fof(f4417,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4416,f3863])).

fof(f3863,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3796])).

fof(f3796,plain,
    ( ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
      | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) )
    & v2_pre_topc(k1_tex_2(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f3654,f3795,f3794])).

fof(f3794,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
              | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
            & v2_pre_topc(k1_tex_2(X0,X1))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(sK0,X1))
            | ~ v1_tdlat_3(k1_tex_2(sK0,X1)) )
          & v2_pre_topc(k1_tex_2(sK0,X1))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3795,plain,
    ( ? [X1] :
        ( ( ~ v2_tdlat_3(k1_tex_2(sK0,X1))
          | ~ v1_tdlat_3(k1_tex_2(sK0,X1)) )
        & v2_pre_topc(k1_tex_2(sK0,X1))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
        | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) )
      & v2_pre_topc(k1_tex_2(sK0,sK1))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3654,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3653])).

fof(f3653,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3646])).

fof(f3646,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_pre_topc(k1_tex_2(X0,X1))
             => ( v2_tdlat_3(k1_tex_2(X0,X1))
                & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3645])).

fof(f3645,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(f4416,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4397,f3864])).

fof(f3864,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3796])).

fof(f4397,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3865,f3989])).

fof(f3989,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3736])).

fof(f3736,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3735])).

fof(f3735,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3596])).

fof(f3596,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f3865,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3796])).

fof(f5141,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5140,f4425])).

fof(f4425,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4424,f3863])).

fof(f4424,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4401,f3864])).

fof(f4401,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3865,f3993])).

fof(f3993,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3738])).

fof(f3738,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3737])).

fof(f3737,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3598])).

fof(f3598,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f5140,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5039,f3866])).

fof(f3866,plain,(
    v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3796])).

fof(f5039,plain,
    ( v1_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f4906,f3936])).

fof(f3936,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3685])).

fof(f3685,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3684])).

fof(f3684,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3558])).

fof(f3558,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_1)).

fof(f4906,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f4421,f4243])).

fof(f4243,plain,(
    ! [X76] :
      ( ~ m1_pre_topc(X76,sK0)
      | l1_pre_topc(X76) ) ),
    inference(resolution,[],[f3864,f4062])).

fof(f4062,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3792])).

fof(f3792,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4421,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f4420,f3863])).

fof(f4420,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4399,f3864])).

fof(f4399,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3865,f3991])).

fof(f3991,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3736])).

fof(f5216,plain,(
    ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f5139,f3867])).

fof(f3867,plain,
    ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f3796])).

fof(f5139,plain,(
    v2_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5138,f4417])).

fof(f5138,plain,
    ( v2_tdlat_3(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5137,f3866])).

fof(f5137,plain,
    ( v2_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5038,f4425])).

fof(f5038,plain,
    ( ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v2_pre_topc(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f4906,f3932])).

fof(f3932,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3683])).

fof(f3683,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3682])).

fof(f3682,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3575])).

fof(f3575,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_tex_1)).
%------------------------------------------------------------------------------

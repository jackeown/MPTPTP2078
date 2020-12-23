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
% DateTime   : Thu Dec  3 13:13:35 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 178 expanded)
%              Number of leaves         :    9 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 (1055 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(subsumption_resolution,[],[f328,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK2,sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X2,X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X2,sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
            & v2_tops_2(X2,sK0)
            & v2_tops_2(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
          & v2_tops_2(X2,sK0)
          & v2_tops_2(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0)
        & v2_tops_2(X2,sK0)
        & v2_tops_2(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
      & v2_tops_2(sK2,sK0)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).

fof(f328,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f327,f40])).

fof(f40,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f327,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f326,f55])).

fof(f55,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f24,f33])).

% (8560)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f326,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f325,f39])).

fof(f39,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f25,f23,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f25,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f325,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f324,f54])).

fof(f54,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f26,f24,f31])).

fof(f26,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f324,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f322,f238])).

fof(f238,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f27,f62,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f23,f24,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f27,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f322,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f30,f58])).

fof(f58,plain,(
    k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_setfam_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
      | ~ v1_tops_2(X2,X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X2,X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              | ~ v1_tops_2(X2,X0)
              | ~ v1_tops_2(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & v1_tops_2(X1,X0) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:49:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8554)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (8555)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (8562)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (8564)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.15/0.51  % (8556)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.15/0.51  % (8563)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.15/0.51  % (8548)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.15/0.52  % (8563)Refutation found. Thanks to Tanya!
% 1.15/0.52  % SZS status Theorem for theBenchmark
% 1.15/0.52  % SZS output start Proof for theBenchmark
% 1.15/0.52  fof(f329,plain,(
% 1.15/0.52    $false),
% 1.15/0.52    inference(subsumption_resolution,[],[f328,f22])).
% 1.15/0.52  fof(f22,plain,(
% 1.15/0.52    l1_pre_topc(sK0)),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f20,plain,(
% 1.15/0.52    ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 1.15/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f19,f18,f17])).
% 1.15/0.52  fof(f17,plain,(
% 1.15/0.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 1.15/0.52    introduced(choice_axiom,[])).
% 1.15/0.52  fof(f18,plain,(
% 1.15/0.52    ? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.15/0.52    introduced(choice_axiom,[])).
% 1.15/0.52  fof(f19,plain,(
% 1.15/0.52    ? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2),sK0) & v2_tops_2(X2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK2,sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 1.15/0.52    introduced(choice_axiom,[])).
% 1.15/0.52  fof(f9,plain,(
% 1.15/0.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.15/0.52    inference(flattening,[],[f8])).
% 1.15/0.52  fof(f8,plain,(
% 1.15/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v2_tops_2(X2,X0) & v2_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 1.15/0.52    inference(ennf_transformation,[],[f7])).
% 1.15/0.52  fof(f7,negated_conjecture,(
% 1.15/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.15/0.52    inference(negated_conjecture,[],[f6])).
% 1.15/0.52  fof(f6,conjecture,(
% 1.15/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).
% 1.15/0.52  fof(f328,plain,(
% 1.15/0.52    ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f327,f40])).
% 1.15/0.52  fof(f40,plain,(
% 1.15/0.52    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f23,f33])).
% 1.15/0.52  fof(f33,plain,(
% 1.15/0.52    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f16])).
% 1.15/0.52  fof(f16,plain,(
% 1.15/0.52    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.52    inference(ennf_transformation,[],[f2])).
% 1.15/0.52  fof(f2,axiom,(
% 1.15/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.15/0.52  fof(f23,plain,(
% 1.15/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f327,plain,(
% 1.15/0.52    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f326,f55])).
% 1.15/0.52  fof(f55,plain,(
% 1.15/0.52    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f24,f33])).
% 1.15/0.52  % (8560)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.15/0.52  fof(f24,plain,(
% 1.15/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f326,plain,(
% 1.15/0.52    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f325,f39])).
% 1.15/0.52  fof(f39,plain,(
% 1.15/0.52    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f22,f25,f23,f31])).
% 1.15/0.52  fof(f31,plain,(
% 1.15/0.52    ( ! [X0,X1] : (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f21])).
% 1.15/0.52  fof(f21,plain,(
% 1.15/0.52    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.15/0.52    inference(nnf_transformation,[],[f15])).
% 1.15/0.52  fof(f15,plain,(
% 1.15/0.52    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.15/0.52    inference(ennf_transformation,[],[f4])).
% 1.15/0.52  fof(f4,axiom,(
% 1.15/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).
% 1.15/0.52  fof(f25,plain,(
% 1.15/0.52    v2_tops_2(sK1,sK0)),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f325,plain,(
% 1.15/0.52    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f324,f54])).
% 1.15/0.52  fof(f54,plain,(
% 1.15/0.52    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0)),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f22,f26,f24,f31])).
% 1.15/0.52  fof(f26,plain,(
% 1.15/0.52    v2_tops_2(sK2,sK0)),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f324,plain,(
% 1.15/0.52    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(subsumption_resolution,[],[f322,f238])).
% 1.15/0.52  fof(f238,plain,(
% 1.15/0.52    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),sK0)),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f22,f27,f62,f32])).
% 1.15/0.52  fof(f32,plain,(
% 1.15/0.52    ( ! [X0,X1] : (v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f21])).
% 1.15/0.52  fof(f62,plain,(
% 1.15/0.52    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f23,f24,f28])).
% 1.15/0.52  fof(f28,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f11])).
% 1.15/0.52  fof(f11,plain,(
% 1.15/0.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.15/0.52    inference(flattening,[],[f10])).
% 1.15/0.52  fof(f10,plain,(
% 1.15/0.52    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.15/0.52    inference(ennf_transformation,[],[f1])).
% 1.15/0.52  fof(f1,axiom,(
% 1.15/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.15/0.52  fof(f27,plain,(
% 1.15/0.52    ~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 1.15/0.52    inference(cnf_transformation,[],[f20])).
% 1.15/0.52  fof(f322,plain,(
% 1.15/0.52    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)),sK0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK2),sK0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 1.15/0.52    inference(superposition,[],[f30,f58])).
% 1.15/0.52  fof(f58,plain,(
% 1.15/0.52    k7_setfam_1(u1_struct_0(sK0),k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),sK2))),
% 1.15/0.52    inference(unit_resulting_resolution,[],[f23,f24,f29])).
% 1.15/0.52  fof(f29,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.15/0.52    inference(cnf_transformation,[],[f12])).
% 1.15/0.52  fof(f12,plain,(
% 1.15/0.52    ! [X0,X1] : (! [X2] : (k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.15/0.52    inference(ennf_transformation,[],[f3])).
% 1.15/0.52  fof(f3,axiom,(
% 1.15/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k4_subset_1(k1_zfmisc_1(X0),X1,X2)) = k4_subset_1(k1_zfmisc_1(X0),k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_setfam_1)).
% 1.15/0.52  fof(f30,plain,(
% 1.15/0.52    ( ! [X2,X0,X1] : (v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X2,X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.15/0.52    inference(cnf_transformation,[],[f14])).
% 1.15/0.52  fof(f14,plain,(
% 1.15/0.52    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | ~v1_tops_2(X2,X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.15/0.52    inference(flattening,[],[f13])).
% 1.15/0.52  fof(f13,plain,(
% 1.15/0.52    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) | (~v1_tops_2(X2,X0) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 1.15/0.52    inference(ennf_transformation,[],[f5])).
% 1.15/0.52  fof(f5,axiom,(
% 1.15/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & v1_tops_2(X1,X0)) => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 1.15/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).
% 1.15/0.52  % SZS output end Proof for theBenchmark
% 1.15/0.52  % (8563)------------------------------
% 1.15/0.52  % (8563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (8563)Termination reason: Refutation
% 1.15/0.52  
% 1.15/0.52  % (8563)Memory used [KB]: 1791
% 1.15/0.52  % (8563)Time elapsed: 0.086 s
% 1.15/0.52  % (8563)------------------------------
% 1.15/0.52  % (8563)------------------------------
% 1.15/0.52  % (8549)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.15/0.52  % (8565)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.15/0.52  % (8545)Success in time 0.155 s
%------------------------------------------------------------------------------

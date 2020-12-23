%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1355+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:48 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 341 expanded)
%              Number of leaves         :    6 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  448 (1891 expanded)
%              Number of equality atoms :    4 (  24 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f161])).

fof(f161,plain,(
    ~ v1_compts_1(sK0) ),
    inference(resolution,[],[f160,f42])).

fof(f42,plain,
    ( ~ v2_compts_1(u1_struct_0(sK0),sK0)
    | ~ v1_compts_1(sK0) ),
    inference(backward_demodulation,[],[f17,f40])).

fof(f40,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f19,f38])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> v2_compts_1(k2_struct_0(X0),X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v1_compts_1(X0)
        <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f21,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f19,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f17,plain,
    ( ~ v2_compts_1(k2_struct_0(sK0),sK0)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f160,plain,(
    v2_compts_1(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f159,f41])).

fof(f41,plain,
    ( v2_compts_1(u1_struct_0(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(backward_demodulation,[],[f16,f40])).

fof(f16,plain,
    ( v2_compts_1(k2_struct_0(sK0),sK0)
    | v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f159,plain,
    ( v2_compts_1(u1_struct_0(sK0),sK0)
    | ~ v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f158,f18])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_compts_1(u1_struct_0(sK0),sK0)
    | ~ v1_compts_1(sK0) ),
    inference(resolution,[],[f157,f45])).

fof(f45,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f44,f38])).

fof(f44,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f20,f40])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(u1_struct_0(X0),X0)
      | ~ v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f156,f36])).

% (29848)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_setfam_1(sK3(X0,X1),X1)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_setfam_1(sK3(X0,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_setfam_1(sK3(X0,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_compts_1(X0)
      | ~ m1_setfam_1(sK3(X0,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(u1_struct_0(X0),X0) ) ),
    inference(resolution,[],[f154,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( m1_setfam_1(sK2(X1,sK3(X1,X2)),u1_struct_0(X1))
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(sK3(X0,X1),X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ v1_tops_2(sK3(X1,X2),X1)
      | m1_setfam_1(sK2(X1,sK3(X1,X2)),u1_struct_0(X1))
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ v1_tops_2(sK3(X1,X2),X1)
      | m1_setfam_1(sK2(X1,sK3(X1,X2)),u1_struct_0(X1))
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_compts_1(X2,X1) ) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ v1_tops_2(X1,X0)
      | m1_setfam_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( v1_finset_1(X2)
                        & m1_setfam_1(X2,u1_struct_0(X0))
                        & r1_tarski(X2,X1) ) )
                & v1_tops_2(X1,X0)
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f37])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_tops_2(sK3(X0,X1),X0)
      | ~ v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f152,f35])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_tops_2(sK3(X0,X1),X0)
      | ~ v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK2(X0,sK3(X0,X1)),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v1_tops_2(sK3(X0,X1),X0)
      | ~ v1_compts_1(X0)
      | ~ m1_setfam_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X1,X0) ) ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X2,X1] :
      ( r1_tarski(sK2(X1,sK3(X1,X2)),sK3(X1,X2))
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f68,f37])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ v1_tops_2(sK3(X1,X2),X1)
      | r1_tarski(sK2(X1,sK3(X1,X2)),sK3(X1,X2))
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK3(X1,X2),u1_struct_0(X1))
      | ~ v1_tops_2(sK3(X1,X2),X1)
      | r1_tarski(sK2(X1,sK3(X1,X2)),sK3(X1,X2))
      | ~ v1_compts_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_compts_1(X2,X1) ) ),
    inference(resolution,[],[f24,f35])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(sK2(X6,X7),sK3(X6,X5))
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_setfam_1(sK2(X6,X7),X5)
      | v2_compts_1(X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ m1_setfam_1(X7,u1_struct_0(X6))
      | ~ v1_tops_2(X7,X6)
      | ~ v1_compts_1(X6) ) ),
    inference(subsumption_resolution,[],[f95,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ v1_tops_2(X1,X0)
      | v1_finset_1(sK2(X0,X1))
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ r1_tarski(sK2(X6,X7),sK3(X6,X5))
      | ~ m1_setfam_1(sK2(X6,X7),X5)
      | ~ v1_finset_1(sK2(X6,X7))
      | v2_compts_1(X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ m1_setfam_1(X7,u1_struct_0(X6))
      | ~ v1_tops_2(X7,X6)
      | ~ v1_compts_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ r1_tarski(sK2(X6,X7),sK3(X6,X5))
      | ~ m1_setfam_1(sK2(X6,X7),X5)
      | ~ v1_finset_1(sK2(X6,X7))
      | v2_compts_1(X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ m1_setfam_1(X7,u1_struct_0(X6))
      | ~ v1_tops_2(X7,X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_compts_1(X6) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(X1,u1_struct_0(X0))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,sK3(X0,X1))
      | ~ m1_setfam_1(X3,X1)
      | ~ v1_finset_1(X3)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f171,plain,(
    v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f170,f18])).

fof(f170,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0) ),
    inference(subsumption_resolution,[],[f169,f160])).

fof(f169,plain,
    ( ~ v2_compts_1(u1_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_compts_1(sK0) ),
    inference(resolution,[],[f168,f45])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f167,f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f167,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(sK1(X0),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(u1_struct_0(X0),X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f165,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK4(X1,X0,sK1(X1)),X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X0,X1)
      | v1_compts_1(X1) ) ),
    inference(subsumption_resolution,[],[f120,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_tops_2(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ v1_tops_2(sK1(X1),X1)
      | m1_setfam_1(sK4(X1,X0,sK1(X1)),X0)
      | ~ v2_compts_1(X0,X1)
      | v1_compts_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ v1_tops_2(sK1(X1),X1)
      | m1_setfam_1(sK4(X1,X0,sK1(X1)),X0)
      | ~ v2_compts_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | v1_compts_1(X1) ) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X2,X1)
      | ~ v1_tops_2(X2,X0)
      | m1_setfam_1(sK4(X0,X1,X2),X1)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK1(X0),X1)
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f164,f29])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(sK1(X0),X1)
      | ~ v1_tops_2(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | v1_compts_1(X0) ) ),
    inference(subsumption_resolution,[],[f163,f27])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(sK1(X0),X1)
      | ~ v1_tops_2(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | v1_compts_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(sK1(X0),X1)
      | ~ v1_tops_2(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_setfam_1(sK4(X0,X1,sK1(X0)),u1_struct_0(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(sK1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | v1_compts_1(X0) ) ),
    inference(resolution,[],[f149,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X1,X0,sK1(X1)),sK1(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X0,X1)
      | v1_compts_1(X1) ) ),
    inference(subsumption_resolution,[],[f112,f29])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ v1_tops_2(sK1(X1),X1)
      | r1_tarski(sK4(X1,X0,sK1(X1)),sK1(X1))
      | ~ v2_compts_1(X0,X1)
      | v1_compts_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_setfam_1(sK1(X1),X0)
      | ~ v1_tops_2(sK1(X1),X1)
      | r1_tarski(sK4(X1,X0,sK1(X1)),sK1(X1))
      | ~ v2_compts_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | v1_compts_1(X1) ) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X2,X1)
      | ~ v1_tops_2(X2,X0)
      | r1_tarski(sK4(X0,X1,X2),X2)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4(X1,X0,X2),sK1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_setfam_1(X2,X0)
      | ~ v1_tops_2(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_compts_1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_setfam_1(sK4(X1,X0,X2),u1_struct_0(X1))
      | v1_compts_1(X1) ) ),
    inference(subsumption_resolution,[],[f148,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_setfam_1(X2,X1)
      | ~ v1_tops_2(X2,X0)
      | v1_finset_1(sK4(X0,X1,X2))
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_setfam_1(X2,X0)
      | ~ v1_tops_2(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_compts_1(X0,X1)
      | ~ r1_tarski(sK4(X1,X0,X2),sK1(X1))
      | ~ m1_setfam_1(sK4(X1,X0,X2),u1_struct_0(X1))
      | ~ v1_finset_1(sK4(X1,X0,X2))
      | v1_compts_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_setfam_1(X2,X0)
      | ~ v1_tops_2(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_compts_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(sK4(X1,X0,X2),sK1(X1))
      | ~ m1_setfam_1(sK4(X1,X0,X2),u1_struct_0(X1))
      | ~ v1_finset_1(sK4(X1,X0,X2))
      | v1_compts_1(X1) ) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,sK1(X0))
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ v1_finset_1(X2)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(X2,X1)
      | ~ v1_tops_2(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1850+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:45 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 123 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 469 expanded)
%              Number of equality atoms :   52 ( 140 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f69])).

fof(f69,plain,(
    u1_pre_topc(sK0) != u1_pre_topc(sK1) ),
    inference(forward_demodulation,[],[f66,f30])).

fof(f30,plain,(
    u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f27,f19])).

fof(f19,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v1_tdlat_3(sK1)
    & v1_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tdlat_3(X1)
            & v1_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ v1_tdlat_3(X1)
        & v1_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v1_tdlat_3(sK1)
      & v1_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tdlat_3(X1)
          & v1_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v1_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v1_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v1_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v1_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tex_2)).

fof(f27,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | ~ v1_tdlat_3(sK0) ),
    inference(resolution,[],[f16,f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tdlat_3)).

% (2207)Refutation not found, incomplete strategy% (2207)------------------------------
% (2207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f37,f62])).

fof(f62,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK1) = X2 ) ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f39,plain,(
    m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f38,f21])).

% (2207)Termination reason: Refutation not found, incomplete strategy
fof(f21,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

% (2207)Memory used [KB]: 6140
fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

% (2207)Time elapsed: 0.042 s
% (2207)------------------------------
% (2207)------------------------------
fof(f38,plain,(
    m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f36,f21])).

fof(f36,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f17,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK1) = X2 ) ),
    inference(forward_demodulation,[],[f53,f21])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK1) = X2 ) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f48,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK1) = X2
      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f25,f18])).

fof(f18,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f37,plain,(
    u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f20,plain,(
    ~ v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( v1_tdlat_3(sK1)
    | u1_pre_topc(sK1) != k9_setfam_1(u1_struct_0(sK1)) ),
    inference(resolution,[],[f17,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X6,X7] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_pre_topc(sK1) = X7 ) ),
    inference(subsumption_resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k9_setfam_1(u1_struct_0(sK1))))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_pre_topc(sK1) = X7 ) ),
    inference(forward_demodulation,[],[f58,f21])).

fof(f58,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(u1_pre_topc(sK1),k9_setfam_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_pre_topc(sK1) = X7 ) ),
    inference(forward_demodulation,[],[f50,f21])).

fof(f50,plain,(
    ! [X6,X7] :
      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X6,X7)
      | u1_pre_topc(sK1) = X7
      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------

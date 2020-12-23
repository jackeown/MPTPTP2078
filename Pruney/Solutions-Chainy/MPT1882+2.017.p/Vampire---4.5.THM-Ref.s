%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:02 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  123 (5001 expanded)
%              Number of leaves         :   16 (1278 expanded)
%              Depth                    :   41
%              Number of atoms          :  515 (42082 expanded)
%              Number of equality atoms :   60 ( 669 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f46,f85,f101,f48,f215,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
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
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
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
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f215,plain,(
    sK1 = sK2(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = sK2(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = sK2(sK0,sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(superposition,[],[f141,f188])).

fof(f188,plain,(
    ! [X4] :
      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)
      | sK1 = sK2(sK0,sK1) ) ),
    inference(resolution,[],[f171,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f171,plain,(
    ! [X0] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))
      | sK1 = sK2(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f169,f158])).

fof(f158,plain,
    ( k1_xboole_0 != sK1
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f157,f46])).

fof(f157,plain,
    ( k1_xboole_0 != sK1
    | ~ l1_pre_topc(sK0)
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f156,f48])).

fof(f156,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f155,f101])).

fof(f155,plain,
    ( k1_xboole_0 != sK1
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f147,f85])).

fof(f147,plain,
    ( k1_xboole_0 != sK1
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = sK2(sK0,sK1) ),
    inference(superposition,[],[f58,f131])).

fof(f131,plain,
    ( k1_xboole_0 = sK2(sK0,sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f128,f60])).

fof(f128,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f127,plain,
    ( sK1 = sK2(sK0,sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f121,f102])).

fof(f102,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f101,f89])).

fof(f89,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f46])).

% (6629)Refutation not found, incomplete strategy% (6629)------------------------------
% (6629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f88,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f87,f48])).

% (6629)Termination reason: Refutation not found, incomplete strategy

% (6629)Memory used [KB]: 6268
% (6629)Time elapsed: 0.149 s
% (6629)------------------------------
% (6629)------------------------------
fof(f87,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2(sK0,sK1))
      | sK2(sK0,sK1) = X0
      | v1_xboole_0(sK2(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f119,plain,(
    v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f117,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f116,f101])).

fof(f116,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f114,f85])).

fof(f114,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f107,f101])).

fof(f107,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(resolution,[],[f98,f85])).

fof(f98,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(sK2(sK0,X0),sK0)
      | v1_zfmisc_1(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X0] :
      ( v3_tex_2(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(sK2(sK0,X0),sK0)
      | v1_zfmisc_1(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f45,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tdlat_3(sK0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_tdlat_3(sK0)
      | v1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f74,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f169,plain,(
    ! [X0] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))
      | k1_xboole_0 = sK1
      | sK1 = sK2(sK0,sK1) ) ),
    inference(superposition,[],[f130,f131])).

fof(f130,plain,(
    ! [X1] :
      ( v1_xboole_0(k3_xboole_0(sK2(sK0,sK1),X1))
      | sK1 = sK2(sK0,sK1) ) ),
    inference(resolution,[],[f128,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

% (6622)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_tarski(k2_tarski(X1,X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f141,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(superposition,[],[f112,f131])).

fof(f112,plain,(
    k1_xboole_0 != k3_xboole_0(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f111,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f111,plain,(
    ~ r1_xboole_0(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f106,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

% (6625)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f106,plain,(
    ~ r1_xboole_0(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f105,f47])).

fof(f105,plain,
    ( ~ r1_xboole_0(sK1,sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f102,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,
    ( v1_xboole_0(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f96,f86])).

fof(f86,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_tdlat_3(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f94,f46])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tdlat_3(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f72,f43])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f50])).

fof(f50,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f82,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f80,f48])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:50:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6611)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.13/0.51  % (6627)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.13/0.52  % (6619)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.13/0.52  % (6608)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.13/0.52  % (6604)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.13/0.53  % (6626)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.13/0.53  % (6618)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.53  % (6610)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (6606)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (6612)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.54  % (6627)Refutation not found, incomplete strategy% (6627)------------------------------
% 1.32/0.54  % (6627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (6609)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.54  % (6605)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (6632)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (6628)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.54  % (6632)Refutation not found, incomplete strategy% (6632)------------------------------
% 1.32/0.54  % (6632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (6632)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (6632)Memory used [KB]: 10746
% 1.32/0.54  % (6632)Time elapsed: 0.139 s
% 1.32/0.54  % (6632)------------------------------
% 1.32/0.54  % (6632)------------------------------
% 1.32/0.54  % (6631)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.54  % (6613)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.54  % (6626)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (6620)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.54  % (6631)Refutation not found, incomplete strategy% (6631)------------------------------
% 1.32/0.54  % (6631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (6631)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (6631)Memory used [KB]: 6268
% 1.32/0.54  % (6631)Time elapsed: 0.136 s
% 1.32/0.54  % (6631)------------------------------
% 1.32/0.54  % (6631)------------------------------
% 1.32/0.54  % (6607)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.55  % (6613)Refutation not found, incomplete strategy% (6613)------------------------------
% 1.32/0.55  % (6613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6624)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.55  % (6630)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (6616)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.55  % (6618)Refutation not found, incomplete strategy% (6618)------------------------------
% 1.32/0.55  % (6618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6618)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6618)Memory used [KB]: 1791
% 1.32/0.55  % (6618)Time elapsed: 0.085 s
% 1.32/0.55  % (6618)------------------------------
% 1.32/0.55  % (6618)------------------------------
% 1.32/0.55  % (6623)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (6633)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.55  % (6629)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.55  % (6633)Refutation not found, incomplete strategy% (6633)------------------------------
% 1.32/0.55  % (6633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6633)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6633)Memory used [KB]: 1791
% 1.32/0.55  % (6633)Time elapsed: 0.137 s
% 1.32/0.55  % (6633)------------------------------
% 1.32/0.55  % (6633)------------------------------
% 1.32/0.55  % (6620)Refutation not found, incomplete strategy% (6620)------------------------------
% 1.32/0.55  % (6620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6620)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6620)Memory used [KB]: 10746
% 1.32/0.55  % (6620)Time elapsed: 0.144 s
% 1.32/0.55  % (6620)------------------------------
% 1.32/0.55  % (6620)------------------------------
% 1.32/0.55  % SZS output start Proof for theBenchmark
% 1.32/0.55  fof(f242,plain,(
% 1.32/0.55    $false),
% 1.32/0.55    inference(unit_resulting_resolution,[],[f46,f85,f101,f48,f215,f58])).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f40,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.32/0.55  fof(f39,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f38,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(rectify,[],[f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f36])).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f10])).
% 1.32/0.55  fof(f10,axiom,(
% 1.32/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.32/0.55  fof(f215,plain,(
% 1.32/0.55    sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(trivial_inequality_removal,[],[f214])).
% 1.32/0.55  fof(f214,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0 | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f212])).
% 1.32/0.55  fof(f212,plain,(
% 1.32/0.55    k1_xboole_0 != k1_xboole_0 | sK1 = sK2(sK0,sK1) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(superposition,[],[f141,f188])).
% 1.32/0.55  fof(f188,plain,(
% 1.32/0.55    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) | sK1 = sK2(sK0,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f171,f60])).
% 1.32/0.55  fof(f60,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f24])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.32/0.55  fof(f171,plain,(
% 1.32/0.55    ( ! [X0] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) | sK1 = sK2(sK0,sK1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f169,f158])).
% 1.32/0.55  fof(f158,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f157,f46])).
% 1.32/0.55  fof(f157,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 | ~l1_pre_topc(sK0) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f156,f48])).
% 1.32/0.55  fof(f156,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f155,f101])).
% 1.32/0.55  fof(f155,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f147,f85])).
% 1.32/0.55  fof(f147,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(superposition,[],[f58,f131])).
% 1.32/0.55  fof(f131,plain,(
% 1.32/0.55    k1_xboole_0 = sK2(sK0,sK1) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(resolution,[],[f128,f60])).
% 1.32/0.55  fof(f128,plain,(
% 1.32/0.55    v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(subsumption_resolution,[],[f127,f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    ~v1_xboole_0(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 1.32/0.55  fof(f33,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f34,plain,(
% 1.32/0.55    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,negated_conjecture,(
% 1.32/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.32/0.55    inference(negated_conjecture,[],[f13])).
% 1.32/0.55  fof(f13,conjecture,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 1.32/0.55  fof(f127,plain,(
% 1.32/0.55    sK1 = sK2(sK0,sK1) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.32/0.55    inference(resolution,[],[f121,f102])).
% 1.32/0.55  fof(f102,plain,(
% 1.32/0.55    r1_tarski(sK1,sK2(sK0,sK1))),
% 1.32/0.55    inference(resolution,[],[f101,f89])).
% 1.32/0.55  fof(f89,plain,(
% 1.32/0.55    ~v2_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f88,f46])).
% 1.32/0.55  % (6629)Refutation not found, incomplete strategy% (6629)------------------------------
% 1.32/0.55  % (6629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  fof(f88,plain,(
% 1.32/0.55    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f87,f48])).
% 1.32/0.55  % (6629)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (6629)Memory used [KB]: 6268
% 1.32/0.55  % (6629)Time elapsed: 0.149 s
% 1.32/0.55  % (6629)------------------------------
% 1.32/0.55  % (6629)------------------------------
% 1.32/0.55  fof(f87,plain,(
% 1.32/0.55    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(resolution,[],[f85,f57])).
% 1.32/0.55  fof(f57,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f121,plain,(
% 1.32/0.55    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | sK2(sK0,sK1) = X0 | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(resolution,[],[f119,f51])).
% 1.32/0.55  fof(f51,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.32/0.55    inference(flattening,[],[f17])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f11])).
% 1.32/0.55  fof(f11,axiom,(
% 1.32/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.32/0.55  fof(f119,plain,(
% 1.32/0.55    v1_zfmisc_1(sK2(sK0,sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f118,f46])).
% 1.32/0.55  fof(f118,plain,(
% 1.32/0.55    v1_zfmisc_1(sK2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f117,f48])).
% 1.32/0.55  fof(f117,plain,(
% 1.32/0.55    v1_zfmisc_1(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f116,f101])).
% 1.32/0.55  fof(f116,plain,(
% 1.32/0.55    v1_zfmisc_1(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f114,f85])).
% 1.32/0.55  fof(f114,plain,(
% 1.32/0.55    v1_zfmisc_1(sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(resolution,[],[f109,f56])).
% 1.32/0.55  fof(f56,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f109,plain,(
% 1.32/0.55    ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f108,f48])).
% 1.32/0.55  fof(f108,plain,(
% 1.32/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f107,f101])).
% 1.32/0.55  fof(f107,plain,(
% 1.32/0.55    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1))),
% 1.32/0.55    inference(resolution,[],[f98,f85])).
% 1.32/0.55  fof(f98,plain,(
% 1.32/0.55    ( ! [X0] : (v3_tex_2(X0,sK0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK2(sK0,X0),sK0) | v1_zfmisc_1(sK2(sK0,X0))) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f97,f46])).
% 1.32/0.55  fof(f97,plain,(
% 1.32/0.55    ( ! [X0] : (v3_tex_2(X0,sK0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK2(sK0,X0),sK0) | v1_zfmisc_1(sK2(sK0,X0))) )),
% 1.32/0.55    inference(resolution,[],[f55,f80])).
% 1.32/0.55  fof(f80,plain,(
% 1.32/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_zfmisc_1(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f79,f45])).
% 1.32/0.55  fof(f45,plain,(
% 1.32/0.55    v2_tdlat_3(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f79,plain,(
% 1.32/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tdlat_3(sK0) | v1_zfmisc_1(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f78,f46])).
% 1.32/0.55  fof(f78,plain,(
% 1.32/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v1_zfmisc_1(X0)) )),
% 1.32/0.55    inference(resolution,[],[f74,f43])).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ~v2_struct_0(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f74,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v1_zfmisc_1(X1)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f73,f59])).
% 1.32/0.55  fof(f59,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f7])).
% 1.32/0.55  fof(f7,axiom,(
% 1.32/0.55    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.32/0.55  fof(f73,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f61,f52])).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(flattening,[],[f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,axiom,(
% 1.32/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.32/0.55  fof(f61,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f41])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(nnf_transformation,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.32/0.55    inference(flattening,[],[f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f12])).
% 1.32/0.55  fof(f12,axiom,(
% 1.32/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.32/0.55  fof(f55,plain,(
% 1.32/0.55    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f169,plain,(
% 1.32/0.55    ( ! [X0] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) | k1_xboole_0 = sK1 | sK1 = sK2(sK0,sK1)) )),
% 1.32/0.55    inference(superposition,[],[f130,f131])).
% 1.32/0.55  fof(f130,plain,(
% 1.32/0.55    ( ! [X1] : (v1_xboole_0(k3_xboole_0(sK2(sK0,sK1),X1)) | sK1 = sK2(sK0,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f128,f76])).
% 1.32/0.55  fof(f76,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 1.32/0.55    inference(superposition,[],[f71,f70])).
% 1.32/0.55  fof(f70,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.32/0.55    inference(definition_unfolding,[],[f63,f64])).
% 1.32/0.55  fof(f64,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f8])).
% 1.32/0.55  % (6622)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  fof(f8,axiom,(
% 1.32/0.55    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.32/0.55  fof(f63,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f5])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.32/0.55  fof(f71,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_xboole_0(k3_tarski(k2_tarski(X1,X0))) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f65,f64])).
% 1.32/0.55  fof(f65,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 1.32/0.55    inference(ennf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).
% 1.32/0.55  fof(f141,plain,(
% 1.32/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | sK1 = sK2(sK0,sK1)),
% 1.32/0.55    inference(superposition,[],[f112,f131])).
% 1.32/0.55  fof(f112,plain,(
% 1.32/0.55    k1_xboole_0 != k3_xboole_0(sK2(sK0,sK1),sK1)),
% 1.32/0.55    inference(resolution,[],[f111,f69])).
% 1.32/0.55  fof(f69,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f42])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.32/0.55    inference(nnf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.32/0.55  fof(f111,plain,(
% 1.32/0.55    ~r1_xboole_0(sK2(sK0,sK1),sK1)),
% 1.32/0.55    inference(resolution,[],[f106,f67])).
% 1.32/0.55  fof(f67,plain,(
% 1.32/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f30])).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.32/0.55  % (6625)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.55  fof(f106,plain,(
% 1.32/0.55    ~r1_xboole_0(sK1,sK2(sK0,sK1))),
% 1.32/0.55    inference(subsumption_resolution,[],[f105,f47])).
% 1.32/0.55  fof(f105,plain,(
% 1.32/0.55    ~r1_xboole_0(sK1,sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.32/0.55    inference(resolution,[],[f102,f66])).
% 1.32/0.55  fof(f66,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.32/0.55    inference(flattening,[],[f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.32/0.55    inference(ennf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.32/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.32/0.55  fof(f48,plain,(
% 1.32/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f101,plain,(
% 1.32/0.55    v2_tex_2(sK1,sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f100,f47])).
% 1.32/0.55  fof(f100,plain,(
% 1.32/0.55    v1_xboole_0(sK1) | v2_tex_2(sK1,sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f99,f48])).
% 1.32/0.55  fof(f99,plain,(
% 1.32/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v2_tex_2(sK1,sK0)),
% 1.32/0.55    inference(resolution,[],[f96,f86])).
% 1.32/0.55  fof(f86,plain,(
% 1.32/0.55    v1_zfmisc_1(sK1)),
% 1.32/0.55    inference(resolution,[],[f85,f49])).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f96,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v2_tex_2(X0,sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f95,f45])).
% 1.32/0.55  fof(f95,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v2_tdlat_3(sK0) | v2_tex_2(X0,sK0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f94,f46])).
% 1.32/0.55  fof(f94,plain,(
% 1.32/0.55    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | v2_tex_2(X0,sK0)) )),
% 1.32/0.55    inference(resolution,[],[f72,f43])).
% 1.32/0.55  fof(f72,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_tex_2(X1,X0)) )),
% 1.32/0.55    inference(subsumption_resolution,[],[f62,f52])).
% 1.32/0.55  fof(f62,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f41])).
% 1.32/0.55  fof(f85,plain,(
% 1.32/0.55    ~v3_tex_2(sK1,sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f84,f50])).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  fof(f84,plain,(
% 1.32/0.55    v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f83,f46])).
% 1.32/0.55  fof(f83,plain,(
% 1.32/0.55    v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(subsumption_resolution,[],[f82,f48])).
% 1.32/0.55  fof(f82,plain,(
% 1.32/0.55    v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.55    inference(resolution,[],[f81,f53])).
% 1.32/0.55  fof(f53,plain,(
% 1.32/0.55    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f40])).
% 1.32/0.55  fof(f81,plain,(
% 1.32/0.55    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.32/0.55    inference(resolution,[],[f80,f48])).
% 1.32/0.55  fof(f46,plain,(
% 1.32/0.55    l1_pre_topc(sK0)),
% 1.32/0.55    inference(cnf_transformation,[],[f35])).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (6626)------------------------------
% 1.32/0.55  % (6626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (6626)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (6626)Memory used [KB]: 6396
% 1.32/0.55  % (6626)Time elapsed: 0.102 s
% 1.32/0.55  % (6626)------------------------------
% 1.32/0.55  % (6626)------------------------------
% 1.32/0.56  % (6603)Success in time 0.188 s
%------------------------------------------------------------------------------

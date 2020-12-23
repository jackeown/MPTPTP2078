%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 140 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   21
%              Number of atoms          :  257 ( 770 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f113,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f109,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f109,plain,(
    r2_hidden(sK3(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

% (25570)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f106,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f105,f34])).

fof(f105,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f103,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f98,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f86,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f31,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f32])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK1(X0,X1),X0)
            & r1_tarski(X1,sK1(X0,X1))
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK1(X0,X1),X0)
        & r1_tarski(X1,sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f33,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X1] :
      ( m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f85,plain,(
    ! [X1] :
      ( m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X1] :
      ( m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f31])).

fof(f79,plain,(
    ! [X1] :
      ( m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (25566)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.47  % (25558)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  % (25566)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f109,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    r2_hidden(sK3(k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f106,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f24])).
% 0.21/0.48  % (25570)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f105,f34])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_xboole_0(X1) | ~r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f103,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f98,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(global_subsumption,[],[f86,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f29])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f30])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v3_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f32])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f33,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK1(X0,X1),X0) & r1_tarski(X1,sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f29])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f30])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f31])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X1] : (m1_subset_1(sK1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f32,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25566)------------------------------
% 0.21/0.48  % (25566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25566)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25566)Memory used [KB]: 5373
% 0.21/0.48  % (25566)Time elapsed: 0.066 s
% 0.21/0.48  % (25566)------------------------------
% 0.21/0.48  % (25566)------------------------------
% 0.21/0.48  % (25562)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (25554)Success in time 0.12 s
%------------------------------------------------------------------------------

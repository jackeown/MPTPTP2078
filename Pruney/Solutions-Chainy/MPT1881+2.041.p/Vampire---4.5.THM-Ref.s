%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:59 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  102 (1051 expanded)
%              Number of leaves         :   15 ( 282 expanded)
%              Depth                    :   22
%              Number of atoms          :  414 (6335 expanded)
%              Number of equality atoms :   27 ( 155 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f145,f233])).

fof(f233,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f228,f212])).

fof(f212,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f161,f201])).

fof(f201,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f79,f159,f157,f160,f200])).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ v3_tex_2(X3,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f176,f183])).

fof(f183,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X7,sK0) ) ),
    inference(subsumption_resolution,[],[f182,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f182,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X7,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f181,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X7,sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f53])).

fof(f53,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f180,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X7,sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f169,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X7,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f68,f94])).

fof(f94,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f88,f91,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f91,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f86,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f54,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,(
    ~ v1_subset_1(k2_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f176,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | ~ v2_tex_2(X2,sK0)
      | X2 = X3
      | ~ v3_tex_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f165,f54])).

fof(f165,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | ~ v2_tex_2(X2,sK0)
      | X2 = X3
      | ~ v3_tex_2(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f63,f94])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | X1 = X3
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).

fof(f48,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f160,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f55,f94])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f157,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f159,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f89,f94])).

fof(f89,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f161,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f82,f94])).

fof(f82,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f228,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f211,f75])).

fof(f75,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f211,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f160,f201])).

fof(f145,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f143,f99])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl3_2 ),
    inference(backward_demodulation,[],[f55,f93])).

fof(f93,plain,
    ( u1_struct_0(sK0) = sK1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f83,f55,f59])).

fof(f83,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f143,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f142,f93])).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f51,f52,f54,f85,f121,f141,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f141,plain,
    ( v2_tex_2(sK1,sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f99,f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tex_2(X0,sK0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tex_2(X0,sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_2 ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v2_tex_2(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_2 ),
    inference(superposition,[],[f68,f93])).

fof(f121,plain,
    ( v1_tops_1(sK1,sK0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f87,f115])).

fof(f115,plain,
    ( sK1 = k2_struct_0(sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f97,f95,f59])).

fof(f95,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1))
    | spl3_2 ),
    inference(backward_demodulation,[],[f91,f93])).

fof(f97,plain,
    ( ~ v1_subset_1(k2_struct_0(sK0),sK1)
    | spl3_2 ),
    inference(backward_demodulation,[],[f88,f93])).

fof(f87,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f54,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).

fof(f85,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f57,f83])).

fof(f57,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f81,f77])).

fof(f56,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (810975232)
% 0.13/0.36  ipcrm: permission denied for id (811008001)
% 0.13/0.37  ipcrm: permission denied for id (811073539)
% 0.13/0.37  ipcrm: permission denied for id (811204616)
% 0.13/0.37  ipcrm: permission denied for id (811237385)
% 0.21/0.38  ipcrm: permission denied for id (811368465)
% 0.21/0.38  ipcrm: permission denied for id (811434003)
% 0.21/0.39  ipcrm: permission denied for id (811565081)
% 0.21/0.39  ipcrm: permission denied for id (811597851)
% 0.21/0.40  ipcrm: permission denied for id (811663391)
% 0.21/0.40  ipcrm: permission denied for id (811696160)
% 0.21/0.40  ipcrm: permission denied for id (811728929)
% 0.21/0.40  ipcrm: permission denied for id (811761698)
% 0.21/0.41  ipcrm: permission denied for id (811892775)
% 0.21/0.41  ipcrm: permission denied for id (811925544)
% 0.21/0.41  ipcrm: permission denied for id (811958313)
% 0.21/0.41  ipcrm: permission denied for id (811991082)
% 0.21/0.41  ipcrm: permission denied for id (812023851)
% 0.21/0.42  ipcrm: permission denied for id (812056620)
% 0.21/0.42  ipcrm: permission denied for id (812089390)
% 0.21/0.43  ipcrm: permission denied for id (812220468)
% 0.21/0.43  ipcrm: permission denied for id (812253238)
% 0.21/0.43  ipcrm: permission denied for id (812286007)
% 0.21/0.43  ipcrm: permission denied for id (812384314)
% 0.21/0.43  ipcrm: permission denied for id (812449852)
% 0.21/0.44  ipcrm: permission denied for id (812482621)
% 0.21/0.44  ipcrm: permission denied for id (812548159)
% 0.21/0.44  ipcrm: permission denied for id (812580929)
% 0.21/0.44  ipcrm: permission denied for id (812646468)
% 0.21/0.45  ipcrm: permission denied for id (812679237)
% 0.21/0.45  ipcrm: permission denied for id (812712006)
% 0.21/0.45  ipcrm: permission denied for id (812744775)
% 0.21/0.45  ipcrm: permission denied for id (812810314)
% 0.21/0.45  ipcrm: permission denied for id (812843083)
% 0.21/0.45  ipcrm: permission denied for id (812875852)
% 0.21/0.46  ipcrm: permission denied for id (812974162)
% 0.21/0.46  ipcrm: permission denied for id (813039700)
% 0.21/0.47  ipcrm: permission denied for id (813105238)
% 0.21/0.47  ipcrm: permission denied for id (813138007)
% 0.21/0.47  ipcrm: permission denied for id (813236316)
% 0.21/0.48  ipcrm: permission denied for id (813269085)
% 0.21/0.48  ipcrm: permission denied for id (813367392)
% 0.21/0.48  ipcrm: permission denied for id (813432930)
% 0.21/0.49  ipcrm: permission denied for id (813629546)
% 0.21/0.49  ipcrm: permission denied for id (813662315)
% 0.21/0.49  ipcrm: permission denied for id (813695084)
% 0.21/0.50  ipcrm: permission denied for id (813727853)
% 0.21/0.50  ipcrm: permission denied for id (813760622)
% 0.21/0.50  ipcrm: permission denied for id (813858930)
% 0.21/0.51  ipcrm: permission denied for id (813957236)
% 0.21/0.51  ipcrm: permission denied for id (813990005)
% 0.21/0.52  ipcrm: permission denied for id (814153852)
% 0.21/0.52  ipcrm: permission denied for id (814186622)
% 0.21/0.52  ipcrm: permission denied for id (814219391)
% 0.37/0.63  % (25816)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.37/0.65  % (25807)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.37/0.65  % (25809)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.37/0.66  % (25807)Refutation found. Thanks to Tanya!
% 0.37/0.66  % SZS status Theorem for theBenchmark
% 0.37/0.66  % (25818)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.37/0.66  % (25823)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.37/0.66  % (25826)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.37/0.66  % (25830)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.37/0.67  % (25812)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.37/0.67  % (25815)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.37/0.67  % (25811)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.37/0.67  % (25819)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.37/0.67  % (25821)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.37/0.67  % (25822)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.37/0.68  % (25831)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.37/0.68  % (25824)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.37/0.68  % (25829)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.37/0.68  % (25833)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.37/0.68  % (25814)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.37/0.68  % (25817)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.37/0.68  % (25813)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.37/0.69  % (25808)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.69  % SZS output start Proof for theBenchmark
% 0.37/0.69  fof(f234,plain,(
% 0.37/0.69    $false),
% 0.37/0.69    inference(avatar_sat_refutation,[],[f84,f145,f233])).
% 0.37/0.69  fof(f233,plain,(
% 0.37/0.69    ~spl3_1 | ~spl3_2),
% 0.37/0.69    inference(avatar_contradiction_clause,[],[f232])).
% 0.37/0.69  fof(f232,plain,(
% 0.37/0.69    $false | (~spl3_1 | ~spl3_2)),
% 0.37/0.69    inference(subsumption_resolution,[],[f228,f212])).
% 0.37/0.69  fof(f212,plain,(
% 0.37/0.69    v1_subset_1(sK1,sK1) | (~spl3_1 | ~spl3_2)),
% 0.37/0.69    inference(backward_demodulation,[],[f161,f201])).
% 0.37/0.69  fof(f201,plain,(
% 0.37/0.69    sK1 = k2_struct_0(sK0) | ~spl3_1),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f79,f159,f157,f160,f200])).
% 0.37/0.69  fof(f200,plain,(
% 0.37/0.69    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X2) | X2 = X3 | ~v3_tex_2(X3,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f176,f183])).
% 0.37/0.69  fof(f183,plain,(
% 0.37/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X7,sK0)) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f182,f51])).
% 0.37/0.69  fof(f51,plain,(
% 0.37/0.69    ~v2_struct_0(sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f43,plain,(
% 0.37/0.69    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.37/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 0.37/0.69  fof(f41,plain,(
% 0.37/0.69    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.37/0.69    introduced(choice_axiom,[])).
% 0.37/0.69  fof(f42,plain,(
% 0.37/0.69    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.37/0.69    introduced(choice_axiom,[])).
% 0.37/0.69  fof(f40,plain,(
% 0.37/0.69    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.37/0.69    inference(flattening,[],[f39])).
% 0.37/0.69  fof(f39,plain,(
% 0.37/0.69    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.37/0.69    inference(nnf_transformation,[],[f25])).
% 0.37/0.69  fof(f25,plain,(
% 0.37/0.69    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.37/0.69    inference(flattening,[],[f24])).
% 0.37/0.69  fof(f24,plain,(
% 0.37/0.69    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.37/0.69    inference(ennf_transformation,[],[f23])).
% 0.37/0.69  fof(f23,negated_conjecture,(
% 0.37/0.69    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.37/0.69    inference(negated_conjecture,[],[f22])).
% 0.37/0.69  fof(f22,conjecture,(
% 0.37/0.69    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.37/0.69  fof(f182,plain,(
% 0.37/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X7,sK0) | v2_struct_0(sK0)) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f181,f52])).
% 0.37/0.69  fof(f52,plain,(
% 0.37/0.69    v2_pre_topc(sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f181,plain,(
% 0.37/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X7,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f180,f53])).
% 0.37/0.69  fof(f53,plain,(
% 0.37/0.69    v1_tdlat_3(sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f180,plain,(
% 0.37/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X7,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f169,f54])).
% 0.37/0.69  fof(f54,plain,(
% 0.37/0.69    l1_pre_topc(sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f169,plain,(
% 0.37/0.69    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X7,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.37/0.69    inference(superposition,[],[f68,f94])).
% 0.37/0.69  fof(f94,plain,(
% 0.37/0.69    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f88,f91,f59])).
% 0.37/0.69  fof(f59,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f44])).
% 0.37/0.69  fof(f44,plain,(
% 0.37/0.69    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.37/0.69    inference(nnf_transformation,[],[f26])).
% 0.37/0.69  fof(f26,plain,(
% 0.37/0.69    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.37/0.69    inference(ennf_transformation,[],[f17])).
% 0.37/0.69  fof(f17,axiom,(
% 0.37/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.37/0.69  fof(f91,plain,(
% 0.37/0.69    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f86,f70])).
% 0.37/0.69  fof(f70,plain,(
% 0.37/0.69    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.37/0.69    inference(cnf_transformation,[],[f35])).
% 0.37/0.69  fof(f35,plain,(
% 0.37/0.69    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f6])).
% 0.37/0.69  fof(f6,axiom,(
% 0.37/0.69    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.37/0.69  fof(f86,plain,(
% 0.37/0.69    l1_struct_0(sK0)),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f54,f69])).
% 0.37/0.69  fof(f69,plain,(
% 0.37/0.69    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f34])).
% 0.37/0.69  fof(f34,plain,(
% 0.37/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f7])).
% 0.37/0.69  fof(f7,axiom,(
% 0.37/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.37/0.69  fof(f88,plain,(
% 0.37/0.69    ~v1_subset_1(k2_struct_0(sK0),u1_struct_0(sK0))),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f86,f60])).
% 0.37/0.69  fof(f60,plain,(
% 0.37/0.69    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f27])).
% 0.37/0.69  fof(f27,plain,(
% 0.37/0.69    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f8])).
% 0.37/0.69  fof(f8,axiom,(
% 0.37/0.69    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.37/0.69  fof(f68,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f33])).
% 0.37/0.69  fof(f33,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.37/0.69    inference(flattening,[],[f32])).
% 0.37/0.69  fof(f32,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.37/0.69    inference(ennf_transformation,[],[f20])).
% 0.37/0.69  fof(f20,axiom,(
% 0.37/0.69    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.37/0.69  fof(f176,plain,(
% 0.37/0.69    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X2) | ~v2_tex_2(X2,sK0) | X2 = X3 | ~v3_tex_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.37/0.69    inference(subsumption_resolution,[],[f165,f54])).
% 0.37/0.69  fof(f165,plain,(
% 0.37/0.69    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X2) | ~v2_tex_2(X2,sK0) | X2 = X3 | ~v3_tex_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.37/0.69    inference(superposition,[],[f63,f94])).
% 0.37/0.69  fof(f63,plain,(
% 0.37/0.69    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | X1 = X3 | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f49])).
% 0.37/0.69  fof(f49,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f47,f48])).
% 0.37/0.69  fof(f48,plain,(
% 0.37/0.69    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/0.69    introduced(choice_axiom,[])).
% 0.37/0.69  fof(f47,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(rectify,[],[f46])).
% 0.37/0.69  fof(f46,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(flattening,[],[f45])).
% 0.37/0.69  fof(f45,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(nnf_transformation,[],[f31])).
% 0.37/0.69  fof(f31,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(flattening,[],[f30])).
% 0.37/0.69  fof(f30,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f18])).
% 0.37/0.69  fof(f18,axiom,(
% 0.37/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.37/0.69  fof(f160,plain,(
% 0.37/0.69    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.37/0.69    inference(backward_demodulation,[],[f55,f94])).
% 0.37/0.69  fof(f55,plain,(
% 0.37/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f157,plain,(
% 0.37/0.69    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.37/0.69    inference(backward_demodulation,[],[f91,f94])).
% 0.37/0.69  fof(f159,plain,(
% 0.37/0.69    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.37/0.69    inference(backward_demodulation,[],[f89,f94])).
% 0.37/0.69  fof(f89,plain,(
% 0.37/0.69    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f55,f73])).
% 0.37/0.69  fof(f73,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f50])).
% 0.37/0.69  fof(f50,plain,(
% 0.37/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.37/0.69    inference(nnf_transformation,[],[f5])).
% 0.37/0.69  fof(f5,axiom,(
% 0.37/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.37/0.69  fof(f79,plain,(
% 0.37/0.69    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.37/0.69    inference(avatar_component_clause,[],[f77])).
% 0.37/0.69  fof(f77,plain,(
% 0.37/0.69    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.37/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.37/0.69  fof(f161,plain,(
% 0.37/0.69    v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_2),
% 0.37/0.69    inference(backward_demodulation,[],[f82,f94])).
% 0.37/0.69  fof(f82,plain,(
% 0.37/0.69    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.37/0.69    inference(avatar_component_clause,[],[f81])).
% 0.37/0.69  fof(f81,plain,(
% 0.37/0.69    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.37/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.37/0.69  fof(f228,plain,(
% 0.37/0.69    ~v1_subset_1(sK1,sK1) | ~spl3_1),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f211,f75])).
% 0.37/0.69  fof(f75,plain,(
% 0.37/0.69    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.37/0.69    inference(equality_resolution,[],[f58])).
% 0.37/0.69  fof(f58,plain,(
% 0.37/0.69    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.37/0.69    inference(cnf_transformation,[],[f44])).
% 0.37/0.69  fof(f211,plain,(
% 0.37/0.69    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_1),
% 0.37/0.69    inference(backward_demodulation,[],[f160,f201])).
% 0.37/0.69  fof(f145,plain,(
% 0.37/0.69    spl3_2),
% 0.37/0.69    inference(avatar_contradiction_clause,[],[f144])).
% 0.37/0.69  fof(f144,plain,(
% 0.37/0.69    $false | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f143,f99])).
% 0.37/0.69  fof(f99,plain,(
% 0.37/0.69    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl3_2),
% 0.37/0.69    inference(backward_demodulation,[],[f55,f93])).
% 0.37/0.69  fof(f93,plain,(
% 0.37/0.69    u1_struct_0(sK0) = sK1 | spl3_2),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f83,f55,f59])).
% 0.37/0.69  fof(f83,plain,(
% 0.37/0.69    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_2),
% 0.37/0.69    inference(avatar_component_clause,[],[f81])).
% 0.37/0.69  fof(f143,plain,(
% 0.37/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl3_2),
% 0.37/0.69    inference(forward_demodulation,[],[f142,f93])).
% 0.37/0.69  fof(f142,plain,(
% 0.37/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f51,f52,f54,f85,f121,f141,f61])).
% 0.37/0.69  fof(f61,plain,(
% 0.37/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f29])).
% 0.37/0.69  fof(f29,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.37/0.69    inference(flattening,[],[f28])).
% 0.37/0.69  fof(f28,plain,(
% 0.37/0.69    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.37/0.69    inference(ennf_transformation,[],[f21])).
% 0.37/0.69  fof(f21,axiom,(
% 0.37/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.37/0.69  fof(f141,plain,(
% 0.37/0.69    v2_tex_2(sK1,sK0) | spl3_2),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f99,f112])).
% 0.37/0.69  fof(f112,plain,(
% 0.37/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tex_2(X0,sK0)) ) | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f111,f51])).
% 0.37/0.69  fof(f111,plain,(
% 0.37/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f110,f52])).
% 0.37/0.69  fof(f110,plain,(
% 0.37/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f109,f53])).
% 0.37/0.69  fof(f109,plain,(
% 0.37/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tex_2(X0,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f108,f54])).
% 0.37/0.69  fof(f108,plain,(
% 0.37/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl3_2),
% 0.37/0.69    inference(superposition,[],[f68,f93])).
% 0.37/0.69  fof(f121,plain,(
% 0.37/0.69    v1_tops_1(sK1,sK0) | spl3_2),
% 0.37/0.69    inference(backward_demodulation,[],[f87,f115])).
% 0.37/0.69  fof(f115,plain,(
% 0.37/0.69    sK1 = k2_struct_0(sK0) | spl3_2),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f97,f95,f59])).
% 0.37/0.69  fof(f95,plain,(
% 0.37/0.69    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK1)) | spl3_2),
% 0.37/0.69    inference(backward_demodulation,[],[f91,f93])).
% 0.37/0.69  fof(f97,plain,(
% 0.37/0.69    ~v1_subset_1(k2_struct_0(sK0),sK1) | spl3_2),
% 0.37/0.69    inference(backward_demodulation,[],[f88,f93])).
% 0.37/0.69  fof(f87,plain,(
% 0.37/0.69    v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.37/0.69    inference(unit_resulting_resolution,[],[f54,f72])).
% 0.37/0.69  fof(f72,plain,(
% 0.37/0.69    ( ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.37/0.69    inference(cnf_transformation,[],[f38])).
% 0.37/0.69  fof(f38,plain,(
% 0.37/0.69    ! [X0] : (v1_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0))),
% 0.37/0.69    inference(ennf_transformation,[],[f14])).
% 0.37/0.69  fof(f14,axiom,(
% 0.37/0.69    ! [X0] : (l1_pre_topc(X0) => v1_tops_1(k2_struct_0(X0),X0))),
% 0.37/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_tops_1)).
% 0.37/0.69  fof(f85,plain,(
% 0.37/0.69    ~v3_tex_2(sK1,sK0) | spl3_2),
% 0.37/0.69    inference(subsumption_resolution,[],[f57,f83])).
% 0.37/0.69  fof(f57,plain,(
% 0.37/0.69    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  fof(f84,plain,(
% 0.37/0.69    spl3_1 | ~spl3_2),
% 0.37/0.69    inference(avatar_split_clause,[],[f56,f81,f77])).
% 0.37/0.69  fof(f56,plain,(
% 0.37/0.69    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.37/0.69    inference(cnf_transformation,[],[f43])).
% 0.37/0.69  % SZS output end Proof for theBenchmark
% 0.37/0.69  % (25807)------------------------------
% 0.37/0.69  % (25807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.69  % (25807)Termination reason: Refutation
% 0.37/0.69  
% 0.37/0.69  % (25807)Memory used [KB]: 10746
% 0.37/0.69  % (25807)Time elapsed: 0.090 s
% 0.37/0.69  % (25807)------------------------------
% 0.37/0.69  % (25807)------------------------------
% 0.37/0.69  % (25647)Success in time 0.332 s
%------------------------------------------------------------------------------

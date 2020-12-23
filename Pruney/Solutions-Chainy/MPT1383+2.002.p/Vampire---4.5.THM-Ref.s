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
% DateTime   : Thu Dec  3 13:15:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 279 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :  390 (1819 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f414,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f205,f413])).

fof(f413,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f411,f46])).

fof(f46,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f411,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f409,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <~> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m1_connsp_2(X2,X0,X1)
                <=> ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f409,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f407,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f132,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f131,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f131,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f127,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f407,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f406,f354])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK3),X0)
        | r2_hidden(sK1,X0) )
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f353,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f353,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f352,f30])).

fof(f352,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f224,f351])).

fof(f351,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f350,f207])).

fof(f207,plain,
    ( r2_hidden(sK1,sK3)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f28,f46])).

fof(f28,plain,
    ( r2_hidden(sK1,sK3)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f350,plain,
    ( ~ r2_hidden(sK1,sK3)
    | m1_connsp_2(sK3,sK0,sK1)
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f349,f30])).

fof(f349,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK3)
        | m1_connsp_2(sK3,sK0,X8) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f348,f51])).

fof(f51,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f348,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X8,sK3)
        | m1_connsp_2(sK3,sK0,X8) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f347,f31])).

fof(f347,plain,
    ( ! [X8] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X8,sK3)
        | m1_connsp_2(sK3,sK0,X8) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f346,f33])).

fof(f346,plain,
    ( ! [X8] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X8,sK3)
        | m1_connsp_2(sK3,sK0,X8) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f314,f32])).

fof(f314,plain,
    ( ! [X8] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X8,sK3)
        | m1_connsp_2(sK3,sK0,X8) )
    | spl5_1 ),
    inference(resolution,[],[f38,f214])).

fof(f214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f25,f46])).

fof(f25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f223,f31])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f222,f33])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f216,f32])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | spl5_1 ),
    inference(resolution,[],[f214,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f406,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f404,f56])).

fof(f56,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f404,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | spl5_1 ),
    inference(resolution,[],[f228,f29])).

fof(f228,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X2)
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X2)) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f218,f33])).

fof(f218,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3,X2)
        | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X2)) )
    | spl5_1 ),
    inference(resolution,[],[f214,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

% (26217)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f205,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f203,f30])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f202,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f93,f77])).

fof(f77,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f76,f33])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f93,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f89,f86])).

fof(f86,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f89,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f24,f47])).

fof(f47,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f24,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_connsp_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f87,f33])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f202,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f189,f47])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK2,sK0,X0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f188,f31])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f187,f33])).

fof(f187,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f182,f32])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X0,k1_tops_1(sK0,sK2))
      | ~ m1_connsp_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f37,f29])).

fof(f57,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f27,f54,f45])).

fof(f27,plain,
    ( r1_tarski(sK3,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f26,f49,f45])).

fof(f26,plain,
    ( v3_pre_topc(sK3,sK0)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (26225)WARNING: option uwaf not known.
% 0.20/0.46  % (26233)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (26229)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (26221)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (26225)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (26221)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f414,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f52,f57,f205,f413])).
% 0.20/0.48  fof(f413,plain,(
% 0.20/0.48    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f412])).
% 0.20/0.48  fof(f412,plain,(
% 0.20/0.48    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f411,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ~m1_connsp_2(sK2,sK0,sK1) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl5_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f411,plain,(
% 0.20/0.48    m1_connsp_2(sK2,sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f409,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((m1_connsp_2(X2,X0,X1) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.20/0.48  fof(f409,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(resolution,[],[f407,f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f132,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f131,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f127,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(resolution,[],[f36,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.48  fof(f407,plain,(
% 0.20/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(resolution,[],[f406,f354])).
% 0.20/0.48  fof(f354,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK3),X0) | r2_hidden(sK1,X0)) ) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(resolution,[],[f353,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f353,plain,(
% 0.20/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f352,f30])).
% 0.20/0.48  fof(f352,plain,(
% 0.20/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(resolution,[],[f224,f351])).
% 0.20/0.48  fof(f351,plain,(
% 0.20/0.48    m1_connsp_2(sK3,sK0,sK1) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f350,f207])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    r2_hidden(sK1,sK3) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f28,f46])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    r2_hidden(sK1,sK3) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f350,plain,(
% 0.20/0.48    ~r2_hidden(sK1,sK3) | m1_connsp_2(sK3,sK0,sK1) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(resolution,[],[f349,f30])).
% 0.20/0.48  fof(f349,plain,(
% 0.20/0.48    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | ~r2_hidden(X8,sK3) | m1_connsp_2(sK3,sK0,X8)) ) | (spl5_1 | ~spl5_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f348,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    v3_pre_topc(sK3,sK0) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl5_2 <=> v3_pre_topc(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f348,plain,(
% 0.20/0.48    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | ~v3_pre_topc(sK3,sK0) | ~r2_hidden(X8,sK3) | m1_connsp_2(sK3,sK0,X8)) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f347,f31])).
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    ( ! [X8] : (v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v3_pre_topc(sK3,sK0) | ~r2_hidden(X8,sK3) | m1_connsp_2(sK3,sK0,X8)) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f346,f33])).
% 0.20/0.48  fof(f346,plain,(
% 0.20/0.48    ( ! [X8] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v3_pre_topc(sK3,sK0) | ~r2_hidden(X8,sK3) | m1_connsp_2(sK3,sK0,X8)) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f314,f32])).
% 0.20/0.48  fof(f314,plain,(
% 0.20/0.48    ( ! [X8] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v3_pre_topc(sK3,sK0) | ~r2_hidden(X8,sK3) | m1_connsp_2(sK3,sK0,X8)) ) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f38,f214])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f25,f46])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_connsp_2(sK3,sK0,X0) | r2_hidden(X0,k1_tops_1(sK0,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f223,f31])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X0)) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f222,f33])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X0)) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f32])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK3)) | ~m1_connsp_2(sK3,sK0,X0)) ) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f214,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f406,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (spl5_1 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f404,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    r1_tarski(sK3,sK2) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl5_3 <=> r1_tarski(sK3,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f404,plain,(
% 0.20/0.48    ~r1_tarski(sK3,sK2) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f228,f29])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X2) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X2))) ) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f218,f33])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3,X2) | r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,X2))) ) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f214,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % (26217)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    $false | ~spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f203,f30])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f202,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f76,f33])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.20/0.48    inference(resolution,[],[f34,f29])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f85,f32])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f33])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.20/0.48    inference(resolution,[],[f39,f29])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f88,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3)) ) | ~spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f24,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_connsp_2(sK2,sK0,sK1) | ~spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2) | ~r2_hidden(sK1,X3) | ~m1_connsp_2(sK2,sK0,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f87,f33])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f40,f29])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_1),
% 0.20/0.48    inference(resolution,[],[f189,f47])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_connsp_2(sK2,sK0,X0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f188,f31])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f187,f33])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f182,f32])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~m1_connsp_2(sK2,sK0,X0)) )),
% 0.20/0.48    inference(resolution,[],[f37,f29])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl5_1 | spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f54,f45])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    r1_tarski(sK3,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl5_1 | spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f49,f45])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    v3_pre_topc(sK3,sK0) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (26221)------------------------------
% 0.20/0.48  % (26221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26221)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (26221)Memory used [KB]: 5500
% 0.20/0.48  % (26221)Time elapsed: 0.012 s
% 0.20/0.48  % (26221)------------------------------
% 0.20/0.48  % (26221)------------------------------
% 0.20/0.48  % (26216)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.48  % (26214)Success in time 0.125 s
%------------------------------------------------------------------------------

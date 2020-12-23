%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:11 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 441 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 (2890 expanded)
%              Number of equality atoms :   19 ( 299 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f372])).

fof(f372,plain,(
    k1_tarski(sK2(sK0,sK1)) != k1_tarski(sK2(sK0,sK1)) ),
    inference(superposition,[],[f278,f92])).

fof(f92,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f83,f69,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f69,plain,(
    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f37,f38,f36,f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (6535)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (6529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

fof(f36,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f70,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f70,plain,(
    r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f40,f38,f37,f36,f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f278,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k1_tarski(sK2(sK0,sK1)) ),
    inference(forward_demodulation,[],[f277,f94])).

fof(f94,plain,(
    k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f91,f92])).

fof(f91,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f70,f69,f34])).

fof(f34,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f277,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f40,f37,f38,f36,f35,f170,f270,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f270,plain,(
    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f39,f38,f40,f171,f170,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f171,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f38,f115,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f115,plain,(
    m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f85,plain,(
    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f70,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f73,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f39,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f170,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f115,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (6519)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (6512)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6538)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (6521)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6518)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (6513)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (6520)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (6512)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (6508)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f375,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f372])).
% 1.34/0.54  fof(f372,plain,(
% 1.34/0.54    k1_tarski(sK2(sK0,sK1)) != k1_tarski(sK2(sK0,sK1))),
% 1.34/0.54    inference(superposition,[],[f278,f92])).
% 1.34/0.54  fof(f92,plain,(
% 1.34/0.54    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k1_tarski(sK2(sK0,sK1))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f83,f69,f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.34/0.54    inference(flattening,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f40,f37,f38,f36,f35,f42])).
% 1.34/0.54  fof(f42,plain,(
% 1.34/0.54    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  % (6535)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  fof(f13,axiom,(
% 1.34/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.34/0.54    inference(flattening,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f15])).
% 1.34/0.55  % (6529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  fof(f15,negated_conjecture,(
% 1.34/0.55    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 1.34/0.55    inference(negated_conjecture,[],[f14])).
% 1.34/0.55  fof(f14,conjecture,(
% 1.34/0.55    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ~v2_tex_2(sK1,sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    v2_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    ~v2_struct_0(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    l1_pre_topc(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f83,plain,(
% 1.34/0.55    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f35,f70,f62])).
% 1.34/0.55  fof(f62,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f33])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.34/0.55  fof(f70,plain,(
% 1.34/0.55    r2_hidden(sK2(sK0,sK1),sK1)),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f40,f38,f37,f36,f35,f43])).
% 1.34/0.55  fof(f43,plain,(
% 1.34/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f19])).
% 1.34/0.55  fof(f278,plain,(
% 1.34/0.55    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k1_tarski(sK2(sK0,sK1))),
% 1.34/0.55    inference(forward_demodulation,[],[f277,f94])).
% 1.34/0.55  fof(f94,plain,(
% 1.34/0.55    k1_tarski(sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))))),
% 1.34/0.55    inference(forward_demodulation,[],[f91,f92])).
% 1.34/0.55  fof(f91,plain,(
% 1.34/0.55    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f70,f69,f34])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f277,plain,(
% 1.34/0.55    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f40,f37,f38,f36,f35,f170,f270,f41])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f19])).
% 1.34/0.55  fof(f270,plain,(
% 1.34/0.55    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0)),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f39,f38,f40,f171,f170,f55])).
% 1.34/0.55  fof(f55,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f12])).
% 1.34/0.55  fof(f12,axiom,(
% 1.34/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 1.34/0.55  fof(f171,plain,(
% 1.34/0.55    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),sK0)),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f40,f38,f115,f49])).
% 1.34/0.55  fof(f49,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f23])).
% 1.34/0.55  fof(f23,plain,(
% 1.34/0.55    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f11])).
% 1.34/0.55  fof(f11,axiom,(
% 1.34/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.34/0.55  fof(f115,plain,(
% 1.34/0.55    m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f85,f61])).
% 1.34/0.55  fof(f61,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.34/0.55  fof(f85,plain,(
% 1.34/0.55    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f73,f70,f52])).
% 1.34/0.55  fof(f52,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.55  fof(f73,plain,(
% 1.34/0.55    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f35,f60])).
% 1.34/0.55  fof(f60,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f6])).
% 1.34/0.55  fof(f6,axiom,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    v3_tdlat_3(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f17])).
% 1.34/0.55  fof(f170,plain,(
% 1.34/0.55    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.55    inference(unit_resulting_resolution,[],[f40,f115,f48])).
% 1.34/0.55  fof(f48,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.34/0.55    inference(flattening,[],[f21])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (6512)------------------------------
% 1.34/0.55  % (6512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (6512)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (6512)Memory used [KB]: 6396
% 1.34/0.55  % (6512)Time elapsed: 0.111 s
% 1.34/0.55  % (6512)------------------------------
% 1.34/0.55  % (6512)------------------------------
% 1.34/0.55  % (6526)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (6507)Success in time 0.186 s
%------------------------------------------------------------------------------

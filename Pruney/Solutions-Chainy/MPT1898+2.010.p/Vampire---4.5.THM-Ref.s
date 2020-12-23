%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 133 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 772 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f44,f46,f93,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f93,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f42,f46,f88,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( k6_domain_1(u1_struct_0(X0),sK1(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1(X0,X1))))
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK1(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1(X0,X1))))
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

fof(f88,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f46,f86])).

fof(f86,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f85,f74])).

fof(f74,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(sK2(sK0,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f73,f39])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(sK2(sK0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f72,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f67,f41])).

fof(f67,plain,(
    ! [X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(sK2(X0,X1),X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK2(X0,X1),X0)
            & r1_tarski(X1,sK2(X0,X1))
            & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f85,plain,(
    ! [X1] :
      ( ~ v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f84,f39])).

fof(f84,plain,(
    ! [X1] :
      ( ~ v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,(
    ! [X1] :
      ( ~ v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X1] :
      ( ~ v3_tex_2(sK2(sK0,X1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).

fof(f24,plain,
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

fof(f15,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21027)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (21027)Refutation not found, incomplete strategy% (21027)------------------------------
% 0.21/0.47  % (21027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (21027)Memory used [KB]: 10618
% 0.21/0.47  % (21027)Time elapsed: 0.060 s
% 0.21/0.47  % (21027)------------------------------
% 0.21/0.47  % (21027)------------------------------
% 0.21/0.48  % (21042)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (21040)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (21026)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (21041)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (21032)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (21034)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (21041)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f46,f93,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f42,f46,f88,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (k6_domain_1(u1_struct_0(X0),sK1(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1(X0,X1)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK1(X0,X1)) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK1(X0,X1)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v2_tex_2(k1_xboole_0,sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2(sK0,X1),sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f39])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2(sK0,X1),sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f40])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2(sK0,X1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f41])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2(sK0,X1),sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f42,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(sK2(X0,X1),X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f39])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f40])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f41])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f42])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f43,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v3_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21041)------------------------------
% 0.21/0.48  % (21041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21041)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21041)Memory used [KB]: 6140
% 0.21/0.48  % (21041)Time elapsed: 0.044 s
% 0.21/0.48  % (21041)------------------------------
% 0.21/0.48  % (21041)------------------------------
% 0.21/0.49  % (21031)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (21030)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (21025)Success in time 0.13 s
%------------------------------------------------------------------------------

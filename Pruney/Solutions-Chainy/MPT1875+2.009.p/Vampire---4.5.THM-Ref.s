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
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 302 expanded)
%              Number of leaves         :   15 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          :  328 (1558 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(resolution,[],[f461,f133])).

% (4212)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (4215)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (4216)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (4221)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (4213)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (4204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (4223)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (4219)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f133,plain,(
    r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f132,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f131,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f124,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(f46,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f461,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(forward_demodulation,[],[f460,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f460,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_subset_1(sK1)) ),
    inference(resolution,[],[f234,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f229,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f229,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f228,f183])).

fof(f183,plain,(
    v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f182,f45])).

fof(f182,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f181,f147])).

fof(f147,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f181,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f180,f46])).

fof(f180,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f179,f147])).

fof(f179,plain,
    ( v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f178,f41])).

fof(f178,plain,
    ( v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f44])).

fof(f177,plain,
    ( v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f159])).

fof(f159,plain,(
    v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f152,f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK0)
      | v1_tdlat_3(X2) ) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X2] :
      ( v1_tdlat_3(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f43,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X2] :
      ( v1_tdlat_3(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X2] :
      ( v1_tdlat_3(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f152,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f145,f44])).

fof(f145,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f165,plain,
    ( v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0)
    | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f152,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f228,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f219,f184])).

fof(f184,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f158,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f158,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f152,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f219,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f62,f147])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (4209)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (4217)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (4218)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (4210)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (4217)Refutation not found, incomplete strategy% (4217)------------------------------
% 0.21/0.49  % (4217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4217)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (4217)Memory used [KB]: 1663
% 0.21/0.49  % (4217)Time elapsed: 0.081 s
% 0.21/0.49  % (4217)------------------------------
% 0.21/0.49  % (4217)------------------------------
% 0.21/0.50  % (4220)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (4207)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (4224)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (4208)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (4224)Refutation not found, incomplete strategy% (4224)------------------------------
% 0.21/0.51  % (4224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4224)Memory used [KB]: 10618
% 0.21/0.51  % (4224)Time elapsed: 0.071 s
% 0.21/0.51  % (4224)------------------------------
% 0.21/0.51  % (4224)------------------------------
% 0.21/0.51  % (4206)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (4214)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (4205)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4214)Refutation not found, incomplete strategy% (4214)------------------------------
% 0.21/0.51  % (4214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4214)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4214)Memory used [KB]: 6140
% 0.21/0.51  % (4214)Time elapsed: 0.079 s
% 0.21/0.51  % (4214)------------------------------
% 0.21/0.51  % (4214)------------------------------
% 0.21/0.51  % (4211)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (4205)Refutation not found, incomplete strategy% (4205)------------------------------
% 0.21/0.51  % (4205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4205)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4205)Memory used [KB]: 10618
% 0.21/0.51  % (4205)Time elapsed: 0.101 s
% 0.21/0.51  % (4205)------------------------------
% 0.21/0.51  % (4205)------------------------------
% 0.21/0.51  % (4208)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(resolution,[],[f461,f133])).
% 0.21/0.51  % (4212)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (4215)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (4216)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4221)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (4213)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (4204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (4223)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (4219)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,sK1),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f36,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,sK1),sK1) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,sK1),sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f124,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f46,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ~v2_tex_2(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f461,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f460,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f460,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k2_subset_1(sK1))) )),
% 0.21/0.53    inference(resolution,[],[f234,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f229,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    v1_xboole_0(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f228,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f45])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f181,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f44])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f45,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f46])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    v2_tex_2(sK1,sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f179,f147])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f41])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f44])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f165,f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f152,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X2] : (~m1_pre_topc(X2,sK0) | v1_tdlat_3(X2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f85,f42])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X2] : (v1_tdlat_3(X2) | ~m1_pre_topc(X2,sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_tdlat_3(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X2] : (v1_tdlat_3(X2) | ~m1_pre_topc(X2,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f70,f44])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2] : (v1_tdlat_3(X2) | ~m1_pre_topc(X2,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f41,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f44])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f45,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    v2_tex_2(u1_struct_0(k1_pre_topc(sK0,sK1)),sK0) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~m1_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f152,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.53  fof(f228,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | ~v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f158,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f152,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f44,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f62,f147])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4208)------------------------------
% 0.21/0.53  % (4208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4208)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4208)Memory used [KB]: 1791
% 0.21/0.53  % (4208)Time elapsed: 0.098 s
% 0.21/0.53  % (4208)------------------------------
% 0.21/0.53  % (4208)------------------------------
% 0.21/0.53  % (4200)Success in time 0.169 s
%------------------------------------------------------------------------------

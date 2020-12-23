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
% DateTime   : Thu Dec  3 13:22:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 ( 394 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f80,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f32,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f33,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,
    ( ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0] : ~ sP0(sK1,X0) ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sP0(sK1,X0)
      | ~ v3_tex_2(sK2(sK1,X0),sK1) ) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_tex_2(X1,sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0] :
      ( sP0(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v2_tex_2(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f48,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X0] :
      ( v2_tex_2(k1_xboole_0,X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_tex_2(k1_xboole_0,X0)
      | sP0(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f21])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (29701)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.43  % (29703)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.43  % (29703)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(subsumption_resolution,[],[f80,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~v2_struct_0(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    v2_struct_0(sK1)),
% 0.22/0.43    inference(subsumption_resolution,[],[f79,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    v2_pre_topc(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.22/0.43    inference(subsumption_resolution,[],[f78,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    v3_tdlat_3(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.22/0.43    inference(subsumption_resolution,[],[f77,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    l1_pre_topc(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.22/0.43    inference(resolution,[],[f76,f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0] : (~sP0(sK1,X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f55,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v3_tex_2(sK2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X0,X1] : ((v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.43    inference(nnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    ( ! [X0] : (~sP0(sK1,X0) | ~v3_tex_2(sK2(sK1,X0),sK1)) )),
% 0.22/0.43    inference(resolution,[],[f37,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tex_2(X1,sK1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f27])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f73,f70])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0] : (v2_tex_2(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f67,f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(resolution,[],[f48,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.43    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.43    inference(resolution,[],[f47,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(resolution,[],[f43,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.43    inference(nnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ( ! [X0] : (v2_tex_2(k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(resolution,[],[f41,f36])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X0] : (~v2_tex_2(k1_xboole_0,X0) | sP0(X0,k1_xboole_0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(resolution,[],[f40,f36])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (sP0(X0,X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.43    inference(definition_folding,[],[f14,f21])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (29703)------------------------------
% 0.22/0.43  % (29703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (29703)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (29703)Memory used [KB]: 5373
% 0.22/0.43  % (29703)Time elapsed: 0.004 s
% 0.22/0.43  % (29703)------------------------------
% 0.22/0.43  % (29703)------------------------------
% 0.22/0.43  % (29695)Success in time 0.067 s
%------------------------------------------------------------------------------

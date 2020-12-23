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
% DateTime   : Thu Dec  3 13:21:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 386 expanded)
%              Number of leaves         :   12 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  257 (2229 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f128,f129])).

fof(f129,plain,(
    ~ v2_tex_2(u1_struct_0(sK2(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f42,f82,f81,f46,f94,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f94,plain,(
    m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f71,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

fof(f71,plain,(
    m1_pre_topc(sK2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f70,plain,
    ( m1_pre_topc(sK2(sK0),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f42])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2(sK0),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK2(X0),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(sK2(X0))
        & v7_struct_0(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & m1_pre_topc(sK2(X0),X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
     => ( v2_pre_topc(sK2(X0))
        & v7_struct_0(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & m1_pre_topc(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v2_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc10_tex_2)).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f81,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f44,f78])).

fof(f78,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f43,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f45,f78])).

fof(f45,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f128,plain,(
    v2_tex_2(u1_struct_0(sK2(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f42,f73,f96,f71,f94,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f96,plain,(
    v1_tdlat_3(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f74,f73,f75,f95,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tex_1)).

fof(f95,plain,(
    l1_pre_topc(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f42,f71,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f75,plain,(
    v2_pre_topc(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v2_pre_topc(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    v7_struct_0(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v7_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ~ v2_struct_0(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:21:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (28219)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (28207)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (28222)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (28222)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f128,f129])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~v2_tex_2(u1_struct_0(sK2(sK0)),sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f42,f82,f81,f46,f94,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    m1_subset_1(u1_struct_0(sK2(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f42,f71,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    m1_pre_topc(sK2(sK0),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f70,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f14])).
% 0.20/0.47  fof(f14,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    m1_pre_topc(sK2(sK0),sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f69,f42])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0),sK0) | v2_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f41,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_pre_topc(sK2(X0),X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0] : ((v2_pre_topc(sK2(X0)) & v7_struct_0(sK2(X0)) & ~v2_struct_0(sK2(X0)) & m1_pre_topc(sK2(X0),X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : (v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) => (v2_pre_topc(sK2(X0)) & v7_struct_0(sK2(X0)) & ~v2_struct_0(sK2(X0)) & m1_pre_topc(sK2(X0),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : (v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : (v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v2_pre_topc(X1) & v1_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc10_tex_2)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(backward_demodulation,[],[f44,f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    k1_xboole_0 = sK1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f43,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    v1_xboole_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ~v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.47    inference(backward_demodulation,[],[f45,f78])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    v2_tex_2(u1_struct_0(sK2(sK0)),sK0)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f42,f73,f96,f71,f94,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    v1_tdlat_3(sK2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f74,f73,f75,f95,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (~v7_struct_0(X0) | v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : ((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ((~v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_tex_1)).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    l1_pre_topc(sK2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f42,f71,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v2_pre_topc(sK2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f41,f42,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (v2_pre_topc(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    v7_struct_0(sK2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f41,f42,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (v7_struct_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~v2_struct_0(sK2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f41,f42,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (28222)------------------------------
% 0.20/0.47  % (28222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (28222)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (28222)Memory used [KB]: 6140
% 0.20/0.47  % (28222)Time elapsed: 0.064 s
% 0.20/0.47  % (28222)------------------------------
% 0.20/0.47  % (28222)------------------------------
% 0.20/0.47  % (28206)Success in time 0.119 s
%------------------------------------------------------------------------------

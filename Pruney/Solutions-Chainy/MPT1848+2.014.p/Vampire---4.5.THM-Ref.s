%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 206 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X1) = u1_struct_0(X0)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X1) = u1_struct_0(X0)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X1) = u1_struct_0(X0)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X1) = u1_struct_0(X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X1) = u1_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

fof(f52,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f51,f17])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f19,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f40,plain,(
    ! [X0] :
      ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_tex_2(sK1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f28,f18])).

fof(f18,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (26832)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.44  % (26828)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.45  % (26828)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(subsumption_resolution,[],[f52,f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    l1_pre_topc(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X1) = u1_struct_0(X0) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X1) = u1_struct_0(X0) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f7])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X1) = u1_struct_0(X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X1) = u1_struct_0(X0))))),
% 0.19/0.45    inference(negated_conjecture,[],[f5])).
% 0.19/0.45  fof(f5,conjecture,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X1) = u1_struct_0(X0))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    ~l1_pre_topc(sK0)),
% 0.19/0.45    inference(subsumption_resolution,[],[f51,f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    m1_pre_topc(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.45    inference(subsumption_resolution,[],[f48,f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    v1_tex_2(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    ~v1_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.19/0.45    inference(resolution,[],[f40,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.19/0.45    inference(backward_demodulation,[],[f20,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X0] : (v1_subset_1(u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_tex_2(sK1,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(superposition,[],[f28,f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(subsumption_resolution,[],[f25,f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(equality_resolution,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (26828)------------------------------
% 0.19/0.45  % (26828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (26828)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (26828)Memory used [KB]: 10618
% 0.19/0.45  % (26828)Time elapsed: 0.043 s
% 0.19/0.45  % (26828)------------------------------
% 0.19/0.45  % (26828)------------------------------
% 0.19/0.45  % (26825)Success in time 0.103 s
%------------------------------------------------------------------------------

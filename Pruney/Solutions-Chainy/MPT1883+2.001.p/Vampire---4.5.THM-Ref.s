%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 407 expanded)
%              Number of leaves         :    6 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  237 (3441 expanded)
%              Number of equality atoms :   32 ( 461 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f64])).

fof(f64,plain,(
    ~ v4_tex_2(sK1,sK0) ),
    inference(resolution,[],[f24,f51])).

fof(f51,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ v4_tex_2(sK1,sK0)
      | ~ v3_tex_2(sK2,sK0) )
    & ( v4_tex_2(sK1,sK0)
      | v3_tex_2(sK2,sK0) )
    & u1_struct_0(sK1) = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) )
                & ( v4_tex_2(X1,X0)
                  | v3_tex_2(X2,X0) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,sK0)
                | ~ v3_tex_2(X2,sK0) )
              & ( v4_tex_2(X1,sK0)
                | v3_tex_2(X2,sK0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v4_tex_2(X1,sK0)
              | ~ v3_tex_2(X2,sK0) )
            & ( v4_tex_2(X1,sK0)
              | v3_tex_2(X2,sK0) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ~ v4_tex_2(sK1,sK0)
            | ~ v3_tex_2(X2,sK0) )
          & ( v4_tex_2(sK1,sK0)
            | v3_tex_2(X2,sK0) )
          & u1_struct_0(sK1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ( ~ v4_tex_2(sK1,sK0)
          | ~ v3_tex_2(X2,sK0) )
        & ( v4_tex_2(sK1,sK0)
          | v3_tex_2(X2,sK0) )
        & u1_struct_0(sK1) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v4_tex_2(sK1,sK0)
        | ~ v3_tex_2(sK2,sK0) )
      & ( v4_tex_2(sK1,sK0)
        | v3_tex_2(sK2,sK0) )
      & u1_struct_0(sK1) = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v4_tex_2(X1,X0)
                | ~ v3_tex_2(X2,X0) )
              & ( v4_tex_2(X1,X0)
                | v3_tex_2(X2,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f5])).

% (3023)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (3016)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (3035)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tex_2(X2,X0)
              <~> v4_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v3_tex_2(X2,X0)
                  <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

fof(f50,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK2,sK0) ),
    inference(forward_demodulation,[],[f49,f22])).

fof(f22,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f48,f23])).

fof(f23,plain,
    ( v3_tex_2(sK2,sK0)
    | v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,
    ( v3_tex_2(sK2,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tex_2(sK1,sK0) ),
    inference(forward_demodulation,[],[f47,f22])).

fof(f47,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK3(X0,X1),X0)
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK3(X0,X1),X0)
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f20,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,
    ( ~ v3_tex_2(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f74,f51])).

fof(f74,plain,
    ( ~ v3_tex_2(sK2,sK0)
    | v4_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f58,f70])).

fof(f70,plain,(
    sK2 = sK3(sK0,sK1) ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,
    ( v4_tex_2(sK1,sK0)
    | sK2 = sK3(sK0,sK1) ),
    inference(forward_demodulation,[],[f55,f22])).

fof(f55,plain,
    ( v4_tex_2(sK1,sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1) ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f54,plain,
    ( v4_tex_2(sK1,sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f44,plain,
    ( v4_tex_2(sK1,sK0)
    | u1_struct_0(sK1) = sK3(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f57,f18])).

fof(f57,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK3(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f45,f19])).

fof(f45,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK3(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK3(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (3018)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (3018)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(resolution,[],[f24,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v3_tex_2(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    (((~v4_tex_2(sK1,sK0) | ~v3_tex_2(sK2,sK0)) & (v4_tex_2(sK1,sK0) | v3_tex_2(sK2,sK0)) & u1_struct_0(sK1) = sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0)) & (v4_tex_2(X1,X0) | v3_tex_2(X2,X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~v4_tex_2(X1,sK0) | ~v3_tex_2(X2,sK0)) & (v4_tex_2(X1,sK0) | v3_tex_2(X2,sK0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : ((~v4_tex_2(X1,sK0) | ~v3_tex_2(X2,sK0)) & (v4_tex_2(X1,sK0) | v3_tex_2(X2,sK0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) => (? [X2] : ((~v4_tex_2(sK1,sK0) | ~v3_tex_2(X2,sK0)) & (v4_tex_2(sK1,sK0) | v3_tex_2(X2,sK0)) & u1_struct_0(sK1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X2] : ((~v4_tex_2(sK1,sK0) | ~v3_tex_2(X2,sK0)) & (v4_tex_2(sK1,sK0) | v3_tex_2(X2,sK0)) & u1_struct_0(sK1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v4_tex_2(sK1,sK0) | ~v3_tex_2(sK2,sK0)) & (v4_tex_2(sK1,sK0) | v3_tex_2(sK2,sK0)) & u1_struct_0(sK1) = sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((~v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0)) & (v4_tex_2(X1,X0) | v3_tex_2(X2,X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((~v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0)) & (v4_tex_2(X1,X0) | v3_tex_2(X2,X0))) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  % (3023)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (3016)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (3035)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((v3_tex_2(X2,X0) <~> v4_tex_2(X1,X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f4])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((v3_tex_2(X2,X0) <~> v4_tex_2(X1,X0)) & u1_struct_0(X1) = X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK2,sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f49,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    u1_struct_0(sK1) = sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v3_tex_2(sK2,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v3_tex_2(sK2,sK0) | v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v3_tex_2(sK2,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f47,f22])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    v3_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v3_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f42,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v3_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f20,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3(X0,X1),X0) & u1_struct_0(X1) = sK3(X0,X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v3_tex_2(sK2,sK0) | ~v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f51])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~v3_tex_2(sK2,sK0) | v4_tex_2(sK1,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f58,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    sK2 = sK3(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f64,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | sK2 = sK3(sK0,sK1)),
% 0.21/0.47    inference(forward_demodulation,[],[f55,f22])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | u1_struct_0(sK1) = sK3(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f18])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | u1_struct_0(sK1) = sK3(sK0,sK1) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f19])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | u1_struct_0(sK1) = sK3(sK0,sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f20,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_tex_2(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | ~v3_tex_2(sK3(sK0,sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f18])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | ~v3_tex_2(sK3(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f45,f19])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v4_tex_2(sK1,sK0) | ~v3_tex_2(sK3(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f20,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(sK3(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (3018)------------------------------
% 0.21/0.47  % (3018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3018)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (3018)Memory used [KB]: 1663
% 0.21/0.47  % (3018)Time elapsed: 0.054 s
% 0.21/0.47  % (3018)------------------------------
% 0.21/0.47  % (3018)------------------------------
% 0.21/0.47  % (3011)Success in time 0.118 s
%------------------------------------------------------------------------------

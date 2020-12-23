%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:35 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 220 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 ( 572 expanded)
%              Number of equality atoms :   34 ( 103 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(backward_demodulation,[],[f61,f64])).

fof(f64,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f62,f61])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(k2_yellow_1(X0)) = X0
      | v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0) ) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_struct_0(k2_yellow_1(X0)),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f58,f40])).

fof(f40,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_struct_0(k2_yellow_1(X0)),k1_zfmisc_1(u1_struct_0(k2_yellow_1(X0)))) ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f57,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f56,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(forward_demodulation,[],[f55,f38])).

fof(f38,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f55,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f61,plain,(
    ! [X1] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1) ),
    inference(forward_demodulation,[],[f59,f40])).

fof(f59,plain,(
    ! [X1] : ~ v1_subset_1(k2_struct_0(k2_yellow_1(X1)),u1_struct_0(k2_yellow_1(X1))) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f86,plain,(
    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f85,f36])).

fof(f36,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( v1_tex_2(sK1,sK0)
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_tex_2(X1,X0)
            & u1_struct_0(X0) = u1_struct_0(X1)
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( v1_tex_2(X1,sK0)
          & u1_struct_0(X1) = u1_struct_0(sK0)
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( v1_tex_2(X1,sK0)
        & u1_struct_0(X1) = u1_struct_0(sK0)
        & m1_pre_topc(X1,sK0) )
   => ( v1_tex_2(sK1,sK0)
      & u1_struct_0(sK0) = u1_struct_0(sK1)
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_tex_2(X1,X0)
          & u1_struct_0(X0) = u1_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ~ ( v1_tex_2(X1,X0)
                & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ~ ( v1_tex_2(X1,X0)
              & u1_struct_0(X0) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

fof(f85,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f84,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f60,f64])).

fof(f84,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f83,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f37,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f81,f35])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ v1_tex_2(X0,sK0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.22/0.52  % (2228)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.53  % (2237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.53  % (2221)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (2228)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % (2231)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.22/0.53  % (2221)Refutation not found, incomplete strategy% (2221)------------------------------
% 1.22/0.53  % (2221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (2221)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (2221)Memory used [KB]: 1791
% 1.22/0.53  % (2221)Time elapsed: 0.116 s
% 1.22/0.53  % (2221)------------------------------
% 1.22/0.53  % (2221)------------------------------
% 1.22/0.53  % (2222)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f87,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(subsumption_resolution,[],[f86,f65])).
% 1.22/0.53  fof(f65,plain,(
% 1.22/0.53    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.22/0.53    inference(backward_demodulation,[],[f61,f64])).
% 1.22/0.53  fof(f64,plain,(
% 1.22/0.53    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f62,f61])).
% 1.22/0.53  fof(f62,plain,(
% 1.22/0.53    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0 | v1_subset_1(k2_struct_0(k2_yellow_1(X0)),X0)) )),
% 1.22/0.53    inference(resolution,[],[f60,f50])).
% 1.22/0.53  fof(f50,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f33])).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.53    inference(nnf_transformation,[],[f24])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f9])).
% 1.22/0.53  fof(f9,axiom,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.22/0.53  fof(f60,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(k2_struct_0(k2_yellow_1(X0)),k1_zfmisc_1(X0))) )),
% 1.22/0.53    inference(forward_demodulation,[],[f58,f40])).
% 1.22/0.53  fof(f40,plain,(
% 1.22/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.22/0.53    inference(cnf_transformation,[],[f7])).
% 1.22/0.53  fof(f7,axiom,(
% 1.22/0.53    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.22/0.53  fof(f58,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(k2_struct_0(k2_yellow_1(X0)),k1_zfmisc_1(u1_struct_0(k2_yellow_1(X0))))) )),
% 1.22/0.53    inference(resolution,[],[f57,f48])).
% 1.22/0.53  fof(f48,plain,(
% 1.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f23])).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.22/0.53  fof(f57,plain,(
% 1.22/0.53    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 1.22/0.53    inference(resolution,[],[f56,f42])).
% 1.22/0.53  fof(f42,plain,(
% 1.22/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f19])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f4])).
% 1.22/0.53  fof(f4,axiom,(
% 1.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.22/0.53  fof(f56,plain,(
% 1.22/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.22/0.53    inference(forward_demodulation,[],[f55,f38])).
% 1.22/0.53  fof(f38,plain,(
% 1.22/0.53    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f5])).
% 1.22/0.53  fof(f5,axiom,(
% 1.22/0.53    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 1.22/0.53  fof(f55,plain,(
% 1.22/0.53    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.22/0.53    inference(resolution,[],[f51,f39])).
% 1.22/0.53  fof(f39,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f15])).
% 1.22/0.53  fof(f15,plain,(
% 1.22/0.53    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.22/0.53    inference(pure_predicate_removal,[],[f14])).
% 1.22/0.53  fof(f14,plain,(
% 1.22/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_relat_2(k1_yellow_1(X0)))),
% 1.22/0.53    inference(pure_predicate_removal,[],[f13])).
% 1.22/0.53  fof(f13,plain,(
% 1.22/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 1.22/0.53    inference(pure_predicate_removal,[],[f12])).
% 1.22/0.53  fof(f12,plain,(
% 1.22/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 1.22/0.53    inference(pure_predicate_removal,[],[f6])).
% 1.22/0.53  fof(f6,axiom,(
% 1.22/0.53    ! [X0] : (m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k1_yellow_1(X0),X0) & v8_relat_2(k1_yellow_1(X0)) & v4_relat_2(k1_yellow_1(X0)) & v1_relat_2(k1_yellow_1(X0)))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).
% 1.22/0.53  fof(f51,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | l1_orders_2(g1_orders_2(X0,X1))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f25])).
% 1.22/0.53  fof(f25,plain,(
% 1.22/0.53    ! [X0,X1] : (l1_orders_2(g1_orders_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.22/0.53    inference(ennf_transformation,[],[f16])).
% 1.22/0.53  fof(f16,plain,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => l1_orders_2(g1_orders_2(X0,X1)))),
% 1.22/0.53    inference(pure_predicate_removal,[],[f3])).
% 1.22/0.53  fof(f3,axiom,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (l1_orders_2(g1_orders_2(X0,X1)) & v1_orders_2(g1_orders_2(X0,X1))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).
% 1.22/0.53  fof(f61,plain,(
% 1.22/0.53    ( ! [X1] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),X1)) )),
% 1.22/0.53    inference(forward_demodulation,[],[f59,f40])).
% 1.22/0.53  fof(f59,plain,(
% 1.22/0.53    ( ! [X1] : (~v1_subset_1(k2_struct_0(k2_yellow_1(X1)),u1_struct_0(k2_yellow_1(X1)))) )),
% 1.22/0.53    inference(resolution,[],[f57,f47])).
% 1.22/0.53  fof(f47,plain,(
% 1.22/0.53    ( ! [X0] : (~l1_struct_0(X0) | ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f22])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 1.22/0.53  fof(f86,plain,(
% 1.22/0.53    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.22/0.53    inference(forward_demodulation,[],[f85,f36])).
% 1.22/0.53  fof(f36,plain,(
% 1.22/0.53    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 1.22/0.53    inference(cnf_transformation,[],[f28])).
% 1.22/0.53  fof(f28,plain,(
% 1.22/0.53    (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f27,plain,(
% 1.22/0.53    ? [X1] : (v1_tex_2(X1,sK0) & u1_struct_0(X1) = u1_struct_0(sK0) & m1_pre_topc(X1,sK0)) => (v1_tex_2(sK1,sK0) & u1_struct_0(sK0) = u1_struct_0(sK1) & m1_pre_topc(sK1,sK0))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.22/0.53    inference(flattening,[],[f17])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : ((v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f11])).
% 1.22/0.53  fof(f11,negated_conjecture,(
% 1.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 1.22/0.53    inference(negated_conjecture,[],[f10])).
% 1.22/0.53  fof(f10,conjecture,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ~(v1_tex_2(X1,X0) & u1_struct_0(X0) = u1_struct_0(X1))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).
% 1.22/0.53  fof(f85,plain,(
% 1.22/0.53    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.22/0.53    inference(subsumption_resolution,[],[f84,f66])).
% 1.22/0.53  fof(f66,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.22/0.53    inference(backward_demodulation,[],[f60,f64])).
% 1.22/0.53  fof(f84,plain,(
% 1.22/0.53    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.22/0.53    inference(forward_demodulation,[],[f83,f36])).
% 1.22/0.53  fof(f83,plain,(
% 1.22/0.53    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.22/0.53    inference(subsumption_resolution,[],[f82,f37])).
% 1.22/0.53  fof(f37,plain,(
% 1.22/0.53    v1_tex_2(sK1,sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f28])).
% 1.22/0.53  fof(f82,plain,(
% 1.22/0.53    ~v1_tex_2(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.22/0.53    inference(resolution,[],[f81,f35])).
% 1.22/0.53  fof(f35,plain,(
% 1.22/0.53    m1_pre_topc(sK1,sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f28])).
% 1.22/0.53  fof(f81,plain,(
% 1.22/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_tex_2(X0,sK0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))) )),
% 1.22/0.53    inference(resolution,[],[f52,f34])).
% 1.22/0.53  fof(f34,plain,(
% 1.22/0.53    l1_pre_topc(sK0)),
% 1.22/0.53    inference(cnf_transformation,[],[f28])).
% 1.22/0.53  fof(f52,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))) )),
% 1.22/0.53    inference(equality_resolution,[],[f43])).
% 1.22/0.53  fof(f43,plain,(
% 1.22/0.53    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f32])).
% 1.22/0.53  fof(f32,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.22/0.53  fof(f31,plain,(
% 1.22/0.53    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f30,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(rectify,[],[f29])).
% 1.22/0.53  fof(f29,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(nnf_transformation,[],[f21])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(flattening,[],[f20])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f8])).
% 1.22/0.53  fof(f8,axiom,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (2228)------------------------------
% 1.22/0.53  % (2228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (2228)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (2228)Memory used [KB]: 6268
% 1.22/0.53  % (2228)Time elapsed: 0.116 s
% 1.22/0.53  % (2228)------------------------------
% 1.22/0.53  % (2228)------------------------------
% 1.29/0.54  % (2215)Success in time 0.171 s
%------------------------------------------------------------------------------

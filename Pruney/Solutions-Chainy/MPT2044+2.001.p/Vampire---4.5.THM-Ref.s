%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 556 expanded)
%              Number of leaves         :    7 ( 195 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (3910 expanded)
%              Number of equality atoms :   25 (  99 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(global_subsumption,[],[f39,f40,f52])).

fof(f52,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    sK2 = sK3(sK2,sK0,sK1) ),
    inference(resolution,[],[f44,f40])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_yellow19(sK0,sK1))
      | sK3(X0,sK0,sK1) = X0 ) ),
    inference(forward_demodulation,[],[f43,f34])).

fof(f34,plain,(
    k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

% (32589)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ r2_hidden(X2,k1_yellow19(sK0,X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | r2_hidden(X2,k1_yellow19(sK0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ r2_hidden(X2,k1_yellow19(sK0,X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | r2_hidden(X2,k1_yellow19(sK0,X1)) ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ r2_hidden(X2,k1_yellow19(sK0,sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | r2_hidden(X2,k1_yellow19(sK0,sK1)) ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ r2_hidden(X2,k1_yellow19(sK0,sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | r2_hidden(X2,k1_yellow19(sK0,sK1)) ) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ r2_hidden(sK2,k1_yellow19(sK0,sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | r2_hidden(sK2,k1_yellow19(sK0,sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <~> m1_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r2_hidden(X2,k1_yellow19(X0,X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow19)).

fof(f33,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow19(sK0,X0) = a_2_0_yellow19(sK0,X0) ) ),
    inference(global_subsumption,[],[f21,f20,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_yellow19(sK0,X0) = a_2_0_yellow19(sK0,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_yellow19(sK0,sK1))
      | sK3(X0,sK0,sK1) = X0 ) ),
    inference(resolution,[],[f42,f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
      | sK3(X0,sK0,X1) = X0 ) ),
    inference(global_subsumption,[],[f21,f20,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK3(X0,sK0,X1) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK3(X0,X1,X2) = X0
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ( sK3(X0,X1,X2) = X0
            & m1_connsp_2(sK3(X0,X1,X2),X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( X0 = X4
          & m1_connsp_2(X4,X1,X2) )
     => ( sK3(X0,X1,X2) = X0
        & m1_connsp_2(sK3(X0,X1,X2),X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X4] :
              ( X0 = X4
              & m1_connsp_2(X4,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X3] :
              ( X0 = X3
              & m1_connsp_2(X3,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

fof(f50,plain,(
    ! [X0] :
      ( m1_connsp_2(sK3(X0,sK0,sK1),sK0,sK1)
      | ~ r2_hidden(X0,k1_yellow19(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f49,f34])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_0_yellow19(sK0,sK1))
      | m1_connsp_2(sK3(X0,sK0,sK1),sK0,sK1) ) ),
    inference(resolution,[],[f48,f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
      | m1_connsp_2(sK3(X0,sK0,X1),sK0,X1) ) ),
    inference(global_subsumption,[],[f21,f20,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow19(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_connsp_2(sK3(X0,sK0,X1),sK0,X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_connsp_2(sK3(X0,X1,X2),X1,X2)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    r2_hidden(sK2,k1_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f24,f39])).

fof(f24,plain,
    ( r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_yellow19(sK0,sK1))
      | ~ m1_connsp_2(X0,sK0,sK1) ) ),
    inference(forward_demodulation,[],[f37,f34])).

fof(f37,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK0,sK1)
      | r2_hidden(X0,a_2_0_yellow19(sK0,sK1)) ) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_connsp_2(X0,sK0,X1)
      | r2_hidden(X0,a_2_0_yellow19(sK0,X1)) ) ),
    inference(global_subsumption,[],[f21,f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_yellow19(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r2_hidden(X3,a_2_0_yellow19(X1,X2))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | X0 != X3
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,
    ( ~ r2_hidden(sK2,k1_yellow19(sK0,sK1))
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:08:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (32587)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (32575)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (32576)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (32587)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f39,f40,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK2,k1_yellow19(sK0,sK1))),
% 0.20/0.51    inference(superposition,[],[f50,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    sK2 = sK3(sK2,sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f44,f40])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_yellow19(sK0,sK1)) | sK3(X0,sK0,sK1) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f43,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)),
% 0.20/0.51    inference(resolution,[],[f33,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    (((~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK2,k1_yellow19(sK0,sK1))) & (m1_connsp_2(sK2,sK0,sK1) | r2_hidden(sK2,k1_yellow19(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).
% 0.20/0.51  % (32589)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1))) & (m1_connsp_2(X2,X0,X1) | r2_hidden(X2,k1_yellow19(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~r2_hidden(X2,k1_yellow19(sK0,X1))) & (m1_connsp_2(X2,sK0,X1) | r2_hidden(X2,k1_yellow19(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~r2_hidden(X2,k1_yellow19(sK0,X1))) & (m1_connsp_2(X2,sK0,X1) | r2_hidden(X2,k1_yellow19(sK0,X1)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(X2,k1_yellow19(sK0,sK1))) & (m1_connsp_2(X2,sK0,sK1) | r2_hidden(X2,k1_yellow19(sK0,sK1)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~r2_hidden(X2,k1_yellow19(sK0,sK1))) & (m1_connsp_2(X2,sK0,sK1) | r2_hidden(X2,k1_yellow19(sK0,sK1)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~r2_hidden(sK2,k1_yellow19(sK0,sK1))) & (m1_connsp_2(sK2,sK0,sK1) | r2_hidden(sK2,k1_yellow19(sK0,sK1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1))) & (m1_connsp_2(X2,X0,X1) | r2_hidden(X2,k1_yellow19(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f5])).
% 0.20/0.51  fof(f5,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f3])).
% 0.20/0.51  fof(f3,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow19)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow19(sK0,X0) = a_2_0_yellow19(sK0,X0)) )),
% 0.20/0.51    inference(global_subsumption,[],[f21,f20,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow19(sK0,X0) = a_2_0_yellow19(sK0,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f26,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,a_2_0_yellow19(sK0,sK1)) | sK3(X0,sK0,sK1) = X0) )),
% 0.20/0.51    inference(resolution,[],[f42,f23])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_0_yellow19(sK0,X1)) | sK3(X0,sK0,X1) = X0) )),
% 0.20/0.51    inference(global_subsumption,[],[f21,f20,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_yellow19(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK3(X0,sK0,X1) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f28,f22])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | sK3(X0,X1,X2) = X0 | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & ((sK3(X0,X1,X2) = X0 & m1_connsp_2(sK3(X0,X1,X2),X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X4] : (X0 = X4 & m1_connsp_2(X4,X1,X2)) => (sK3(X0,X1,X2) = X0 & m1_connsp_2(sK3(X0,X1,X2),X1,X2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & (? [X4] : (X0 = X4 & m1_connsp_2(X4,X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(rectify,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & (? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (m1_connsp_2(sK3(X0,sK0,sK1),sK0,sK1) | ~r2_hidden(X0,k1_yellow19(sK0,sK1))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f49,f34])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,a_2_0_yellow19(sK0,sK1)) | m1_connsp_2(sK3(X0,sK0,sK1),sK0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f48,f23])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_0_yellow19(sK0,X1)) | m1_connsp_2(sK3(X0,sK0,X1),sK0,X1)) )),
% 0.20/0.51    inference(global_subsumption,[],[f21,f20,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_yellow19(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(sK3(X0,sK0,X1),sK0,X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f27,f22])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_connsp_2(sK3(X0,X1,X2),X1,X2) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_yellow19(sK0,sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f24,f39])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_yellow19(sK0,sK1)) | m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f25,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_yellow19(sK0,sK1)) | ~m1_connsp_2(X0,sK0,sK1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f37,f34])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(X0,a_2_0_yellow19(sK0,sK1))) )),
% 0.20/0.51    inference(resolution,[],[f36,f23])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_connsp_2(X0,sK0,X1) | r2_hidden(X0,a_2_0_yellow19(sK0,X1))) )),
% 0.20/0.51    inference(global_subsumption,[],[f21,f20,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,a_2_0_yellow19(sK0,X1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(resolution,[],[f30,f22])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~l1_pre_topc(X1) | ~m1_connsp_2(X3,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | r2_hidden(X3,a_2_0_yellow19(X1,X2)) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_yellow19(X1,X2)) | X0 != X3 | ~m1_connsp_2(X3,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_yellow19(sK0,sK1)) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (32587)------------------------------
% 0.20/0.51  % (32587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32587)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (32587)Memory used [KB]: 6140
% 0.20/0.51  % (32587)Time elapsed: 0.091 s
% 0.20/0.51  % (32587)------------------------------
% 0.20/0.51  % (32587)------------------------------
% 0.20/0.51  % (32572)Success in time 0.153 s
%------------------------------------------------------------------------------

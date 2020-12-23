%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   17
%              Number of atoms          :  125 ( 209 expanded)
%              Number of equality atoms :   46 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f30])).

% (11624)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ~ r1_tarski(k1_xboole_0,sK1(k1_xboole_0)) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f67,plain,(
    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f62,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK1(X0),X0)
          & k1_xboole_0 != sK1(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK1(X0),X0)
        & k1_xboole_0 != sK1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f62,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(superposition,[],[f29,f60])).

fof(f60,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f33,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f58,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)
    | ~ l1_orders_2(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f55,plain,(
    k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
      | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) ) ),
    inference(forward_demodulation,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f45,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) ) ),
    inference(subsumption_resolution,[],[f44,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f44,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f26,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_1)).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (11619)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (11626)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (11612)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (11615)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (11615)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f30])).
% 0.21/0.51  % (11624)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,sK1(k1_xboole_0))),
% 0.21/0.51    inference(resolution,[],[f67,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f62,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = k3_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (((r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK1(X0),X0) & k1_xboole_0 != sK1(X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.21/0.51    inference(rectify,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f29,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) | ~l1_orders_2(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.51    inference(superposition,[],[f55,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f46,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f45,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f44,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f43,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f26,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (11615)------------------------------
% 0.21/0.51  % (11615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11615)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (11615)Memory used [KB]: 1663
% 0.21/0.51  % (11615)Time elapsed: 0.079 s
% 0.21/0.51  % (11615)------------------------------
% 0.21/0.51  % (11615)------------------------------
% 0.21/0.51  % (11609)Success in time 0.161 s
%------------------------------------------------------------------------------

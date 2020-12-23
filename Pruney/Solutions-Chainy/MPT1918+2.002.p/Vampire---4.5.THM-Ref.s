%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 197 expanded)
%              Number of leaves         :    7 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 804 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(global_subsumption,[],[f53,f56])).

fof(f56,plain,(
    ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f30,f20,f47,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f47,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f38,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f38,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f36,f26])).

fof(f26,plain,(
    l1_orders_2(sK1) ),
    inference(unit_resulting_resolution,[],[f17,f18,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f18,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    & m1_yellow_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow_0(X2,X0)
                & m1_yellow_0(X2,X1) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,sK0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow_0(X2,sK0)
            & m1_yellow_0(X2,X1) )
        & m1_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_yellow_0(X2,sK0)
          & m1_yellow_0(X2,sK1) )
      & m1_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ m1_yellow_0(X2,sK0)
        & m1_yellow_0(X2,sK1) )
   => ( ~ m1_yellow_0(sK2,sK0)
      & m1_yellow_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_0(X2,X1)
               => m1_yellow_0(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).

fof(f36,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f21,f24])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f18,f32])).

fof(f20,plain,(
    ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    l1_orders_2(sK2) ),
    inference(global_subsumption,[],[f29,f28])).

fof(f28,plain,
    ( l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f24,f19])).

fof(f29,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f27,f17])).

fof(f27,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f24,f18])).

fof(f17,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f45,f25])).

fof(f45,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f43,f26])).

fof(f43,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f39,f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f18,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (30127)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.45  % (30119)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (30112)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.46  % (30107)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (30127)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (30120)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (30115)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(global_subsumption,[],[f53,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f30,f20,f47,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f33,f38,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f36,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    l1_orders_2(sK1)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f18,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    m1_yellow_0(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ((~m1_yellow_0(sK2,sK0) & m1_yellow_0(sK2,sK1)) & m1_yellow_0(sK1,sK0)) & l1_orders_2(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow_0(X2,X0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,X0)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,sK0)) & l1_orders_2(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,sK0)) => (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,sK1)) & m1_yellow_0(sK1,sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,sK1)) => (~m1_yellow_0(sK2,sK0) & m1_yellow_0(sK2,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow_0(X2,X0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,X0)) & l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 0.20/0.47    inference(negated_conjecture,[],[f4])).
% 0.20/0.47  fof(f4,conjecture,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_orders_2(sK1)),
% 0.20/0.47    inference(resolution,[],[f32,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    m1_yellow_0(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f21,f24])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f18,f32])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ~m1_yellow_0(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    l1_orders_2(sK2)),
% 0.20/0.47    inference(global_subsumption,[],[f29,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    l1_orders_2(sK2) | ~l1_orders_2(sK1)),
% 0.20/0.47    inference(resolution,[],[f24,f19])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    l1_orders_2(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f27,f17])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    l1_orders_2(sK1) | ~l1_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f24,f18])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    l1_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f40,f45,f25])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f43,f26])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | ~l1_orders_2(sK1)),
% 0.20/0.47    inference(resolution,[],[f39,f19])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f22,f24])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f17,f18,f39])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (30127)------------------------------
% 0.20/0.47  % (30127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30127)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (30127)Memory used [KB]: 5373
% 0.20/0.47  % (30127)Time elapsed: 0.059 s
% 0.20/0.47  % (30127)------------------------------
% 0.20/0.47  % (30127)------------------------------
% 0.20/0.47  % (30106)Success in time 0.119 s
%------------------------------------------------------------------------------

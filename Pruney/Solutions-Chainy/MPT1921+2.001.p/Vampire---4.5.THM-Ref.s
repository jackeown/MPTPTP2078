%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  84 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 274 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f28,f39,f40])).

fof(f40,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK2) ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f37,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(global_subsumption,[],[f16,f15,f36])).

fof(f36,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_6)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f15,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(global_subsumption,[],[f16,f15,f37,f38])).

fof(f38,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f21,f13])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f28,plain,
    ( ~ l1_orders_2(sK2)
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(global_subsumption,[],[f26,f27])).

fof(f27,plain,
    ( ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1)
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f26,plain,(
    l1_orders_2(sK1) ),
    inference(global_subsumption,[],[f16,f25])).

fof(f25,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f20,f15])).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.31  % Computer   : n001.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 19:03:45 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.43  % (6221)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.18/0.44  % (6221)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f41,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(global_subsumption,[],[f16,f28,f39,f40])).
% 0.18/0.44  fof(f40,plain,(
% 0.18/0.44    ~l1_struct_0(sK0) | l1_orders_2(sK2)),
% 0.18/0.44    inference(resolution,[],[f37,f20])).
% 0.18/0.44  fof(f20,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f9])).
% 0.18/0.44  fof(f9,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f2])).
% 0.18/0.44  fof(f2,axiom,(
% 0.18/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.18/0.44  fof(f37,plain,(
% 0.18/0.44    l1_waybel_0(sK2,sK0)),
% 0.18/0.44    inference(global_subsumption,[],[f16,f15,f36])).
% 0.18/0.44  fof(f36,plain,(
% 0.18/0.44    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | l1_waybel_0(sK2,sK0)),
% 0.18/0.44    inference(resolution,[],[f24,f13])).
% 0.18/0.44  fof(f13,plain,(
% 0.18/0.44    m1_yellow_6(sK2,sK0,sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f7])).
% 0.18/0.44  fof(f7,plain,(
% 0.18/0.44    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f6])).
% 0.18/0.44  fof(f6,negated_conjecture,(
% 0.18/0.44    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))))),
% 0.18/0.44    inference(negated_conjecture,[],[f5])).
% 0.18/0.44  fof(f5,conjecture,(
% 0.18/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_6)).
% 0.18/0.44  fof(f24,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_waybel_0(X2,X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f12])).
% 0.18/0.44  fof(f12,plain,(
% 0.18/0.44    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.18/0.44    inference(flattening,[],[f11])).
% 0.18/0.44  fof(f11,plain,(
% 0.18/0.44    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.18/0.44    inference(ennf_transformation,[],[f4])).
% 0.18/0.44  fof(f4,axiom,(
% 0.18/0.44    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.18/0.44  fof(f15,plain,(
% 0.18/0.44    l1_waybel_0(sK1,sK0)),
% 0.18/0.44    inference(cnf_transformation,[],[f7])).
% 0.18/0.44  fof(f39,plain,(
% 0.18/0.44    m1_yellow_0(sK2,sK1)),
% 0.18/0.44    inference(global_subsumption,[],[f16,f15,f37,f38])).
% 0.18/0.44  fof(f38,plain,(
% 0.18/0.44    ~l1_waybel_0(sK1,sK0) | ~l1_waybel_0(sK2,sK0) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.18/0.44    inference(resolution,[],[f21,f13])).
% 0.18/0.44  fof(f21,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_waybel_0(X2,X0) | m1_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f3])).
% 0.18/0.44  fof(f3,axiom,(
% 0.18/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.18/0.44  fof(f28,plain,(
% 0.18/0.44    ~l1_orders_2(sK2) | ~m1_yellow_0(sK2,sK1)),
% 0.18/0.44    inference(global_subsumption,[],[f26,f27])).
% 0.18/0.44  fof(f27,plain,(
% 0.18/0.44    ~l1_orders_2(sK2) | ~l1_orders_2(sK1) | ~m1_yellow_0(sK2,sK1)),
% 0.18/0.44    inference(resolution,[],[f17,f14])).
% 0.18/0.44  fof(f14,plain,(
% 0.18/0.44    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.18/0.44    inference(cnf_transformation,[],[f7])).
% 0.18/0.44  fof(f17,plain,(
% 0.18/0.44    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f8])).
% 0.18/0.44  fof(f8,plain,(
% 0.18/0.44    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.18/0.44    inference(ennf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.18/0.44  fof(f26,plain,(
% 0.18/0.44    l1_orders_2(sK1)),
% 0.18/0.44    inference(global_subsumption,[],[f16,f25])).
% 0.18/0.44  fof(f25,plain,(
% 0.18/0.44    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.18/0.44    inference(resolution,[],[f20,f15])).
% 0.18/0.44  fof(f16,plain,(
% 0.18/0.44    l1_struct_0(sK0)),
% 0.18/0.44    inference(cnf_transformation,[],[f7])).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (6221)------------------------------
% 0.18/0.44  % (6221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (6221)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (6221)Memory used [KB]: 10618
% 0.18/0.44  % (6221)Time elapsed: 0.057 s
% 0.18/0.44  % (6221)------------------------------
% 0.18/0.44  % (6221)------------------------------
% 0.18/0.44  % (6208)Success in time 0.11 s
%------------------------------------------------------------------------------

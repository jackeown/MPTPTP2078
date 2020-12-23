%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 218 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  198 (1492 expanded)
%              Number of equality atoms :   12 ( 230 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f65])).

fof(f65,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f27,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X2,X5,X6)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X2,X5,X6)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).

fof(f64,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f63,f56])).

fof(f56,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_yellow_6(X0,sK0,sK1)
      | l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f54,f27])).

% (22745)Refutation not found, incomplete strategy% (22745)------------------------------
% (22745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ m1_yellow_6(X1,sK0,X0)
      | l1_waybel_0(X1,sK0) ) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f63,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(resolution,[],[f62,f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_6(X1,sK0,X0)
      | ~ l1_waybel_0(X1,sK0)
      | m1_yellow_0(X1,X0)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f33,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f101,plain,(
    ~ m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(resolution,[],[f46,f27])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f100,plain,
    ( ~ l1_orders_2(sK1)
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(subsumption_resolution,[],[f99,f58])).

fof(f58,plain,(
    l1_orders_2(sK2) ),
    inference(resolution,[],[f56,f46])).

fof(f99,plain,
    ( ~ l1_orders_2(sK2)
    | ~ l1_orders_2(sK1)
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f98,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f98,plain,(
    ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f97,f22])).

fof(f22,plain,(
    ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(subsumption_resolution,[],[f96,f47])).

fof(f96,plain,
    ( ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | r1_orders_2(sK1,sK3,sK4) ),
    inference(resolution,[],[f79,f24])).

fof(f24,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK4,u1_struct_0(X2))
      | ~ m1_subset_1(sK3,u1_struct_0(X2))
      | ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(X2))
      | ~ l1_orders_2(X2)
      | r1_orders_2(X2,sK3,sK4) ) ),
    inference(resolution,[],[f77,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3,sK4),X0)
      | ~ r1_tarski(u1_orders_2(sK2),X0) ) ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f74,plain,(
    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f73,f58])).

fof(f73,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f72,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f18,f20])).

fof(f20,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f23,f19])).

fof(f19,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f37,f43])).

fof(f43,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f42,f19])).

fof(f42,plain,(
    r1_orders_2(sK2,sK5,sK4) ),
    inference(backward_demodulation,[],[f21,f20])).

fof(f21,plain,(
    r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (22745)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (22734)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (22734)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    m1_yellow_0(sK2,sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f64,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    l1_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X1,X3,X4) & (r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_6)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    m1_yellow_0(sK2,sK1) | ~l1_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f63,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    l1_waybel_0(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f55,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    m1_yellow_6(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f54,f27])).
% 0.20/0.51  % (22745)Refutation not found, incomplete strategy% (22745)------------------------------
% 0.20/0.51  % (22745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~m1_yellow_6(X1,sK0,X0) | l1_waybel_0(X1,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f38,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m1_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~l1_waybel_0(sK2,sK0) | m1_yellow_0(sK2,sK1) | ~l1_waybel_0(sK1,sK0)),
% 0.20/0.51    inference(resolution,[],[f62,f26])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_yellow_6(X1,sK0,X0) | ~l1_waybel_0(X1,sK0) | m1_yellow_0(X1,X0) | ~l1_waybel_0(X0,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f33,f28])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~l1_waybel_0(X2,X0) | m1_yellow_0(X2,X1) | ~m1_yellow_6(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~m1_yellow_0(sK2,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    l1_orders_2(sK1)),
% 0.20/0.51    inference(resolution,[],[f46,f27])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | l1_orders_2(X0)) )),
% 0.20/0.51    inference(resolution,[],[f32,f28])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | l1_orders_2(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ~l1_orders_2(sK1) | ~m1_yellow_0(sK2,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    l1_orders_2(sK2)),
% 0.20/0.51    inference(resolution,[],[f56,f46])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ~l1_orders_2(sK2) | ~l1_orders_2(sK1) | ~m1_yellow_0(sK2,sK1)),
% 0.20/0.51    inference(resolution,[],[f98,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))),
% 0.20/0.51    inference(subsumption_resolution,[],[f97,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ~r1_orders_2(sK1,sK3,sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | r1_orders_2(sK1,sK3,sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f96,f47])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | ~l1_orders_2(sK1) | r1_orders_2(sK1,sK3,sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | ~l1_orders_2(sK1) | r1_orders_2(sK1,sK3,sK4)),
% 0.20/0.51    inference(resolution,[],[f79,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(sK4,u1_struct_0(X2)) | ~m1_subset_1(sK3,u1_struct_0(X2)) | ~r1_tarski(u1_orders_2(sK2),u1_orders_2(X2)) | ~l1_orders_2(X2) | r1_orders_2(X2,sK3,sK4)) )),
% 0.20/0.51    inference(resolution,[],[f77,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k4_tarski(sK3,sK4),X0) | ~r1_tarski(u1_orders_2(sK2),X0)) )),
% 0.20/0.51    inference(resolution,[],[f74,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f73,f58])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f72,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.20/0.51    inference(forward_demodulation,[],[f18,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    sK4 = sK6),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ~m1_subset_1(sK4,u1_struct_0(sK2)) | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.51    inference(backward_demodulation,[],[f23,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    sK3 = sK5),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.51    inference(resolution,[],[f37,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    r1_orders_2(sK2,sK3,sK4)),
% 0.20/0.51    inference(backward_demodulation,[],[f42,f19])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    r1_orders_2(sK2,sK5,sK4)),
% 0.20/0.51    inference(backward_demodulation,[],[f21,f20])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    r1_orders_2(sK2,sK5,sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (22734)------------------------------
% 0.20/0.51  % (22734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22734)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (22734)Memory used [KB]: 6268
% 0.20/0.51  % (22734)Time elapsed: 0.074 s
% 0.20/0.51  % (22734)------------------------------
% 0.20/0.51  % (22734)------------------------------
% 0.20/0.51  % (22727)Success in time 0.152 s
%------------------------------------------------------------------------------

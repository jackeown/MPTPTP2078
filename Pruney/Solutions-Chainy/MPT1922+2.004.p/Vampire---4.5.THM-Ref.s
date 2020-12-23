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
% DateTime   : Thu Dec  3 13:22:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 180 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 (1285 expanded)
%              Number of equality atoms :   12 ( 198 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(global_subsumption,[],[f43,f46,f53,f55,f175])).

fof(f175,plain,
    ( ~ l1_orders_2(sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_yellow_0(sK2,sK1) ),
    inference(resolution,[],[f118,f45])).

fof(f45,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(forward_demodulation,[],[f44,f20])).

fof(f20,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

fof(f44,plain,(
    r1_orders_2(sK2,sK5,sK4) ),
    inference(forward_demodulation,[],[f22,f21])).

fof(f21,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f11])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_orders_2(X0,sK3,sK4)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_yellow_0(X0,sK1) ) ),
    inference(global_subsumption,[],[f48,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3,sK4)
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ l1_orders_2(sK1)
      | ~ m1_yellow_0(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3,sK4)
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1)
      | ~ m1_yellow_0(X0,sK1) ) ),
    inference(resolution,[],[f74,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_orders_2(X0),u1_orders_2(sK1))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3,sK4)
      | ~ m1_subset_1(sK3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(u1_orders_2(sK1)))
      | ~ m1_subset_1(sK3,u1_struct_0(X0))
      | ~ m1_subset_1(sK4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3,sK4) ) ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3,sK4),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1))) ) ),
    inference(global_subsumption,[],[f25,f26,f48,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ r2_hidden(k4_tarski(sK3,sK4),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1))) ) ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(k4_tarski(X0,X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_orders_2(X1))) ) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    l1_orders_2(sK1) ),
    inference(global_subsumption,[],[f29,f47])).

fof(f47,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(global_subsumption,[],[f29,f28,f51,f54])).

fof(f54,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f51,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(global_subsumption,[],[f29,f28,f50])).

fof(f50,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f40,f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f53,plain,(
    l1_orders_2(sK2) ),
    inference(global_subsumption,[],[f29,f52])).

% (16700)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% (16708)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (16696)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% (16701)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (16711)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (16704)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f52,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK2) ),
    inference(resolution,[],[f51,f33])).

fof(f46,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f24,f20])).

fof(f24,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f19,f21])).

fof(f19,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16694)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (16693)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (16702)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (16693)Refutation not found, incomplete strategy% (16693)------------------------------
% 0.21/0.50  % (16693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16695)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (16705)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (16699)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (16691)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (16692)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (16712)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (16709)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (16693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16693)Memory used [KB]: 10618
% 0.21/0.51  % (16693)Time elapsed: 0.096 s
% 0.21/0.51  % (16693)------------------------------
% 0.21/0.51  % (16693)------------------------------
% 0.21/0.51  % (16702)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f43,f46,f53,f55,f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~l1_orders_2(sK2) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_yellow_0(sK2,sK1)),
% 0.21/0.51    inference(resolution,[],[f118,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f44,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    sK3 = sK5),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X1,X3,X4) & (r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r1_orders_2(sK2,sK5,sK4)),
% 0.21/0.51    inference(forward_demodulation,[],[f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    sK4 = sK6),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    r1_orders_2(sK2,sK5,sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_orders_2(X0,sK3,sK4) | ~l1_orders_2(X0) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_yellow_0(X0,sK1)) )),
% 0.21/0.51    inference(global_subsumption,[],[f48,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,sK3,sK4) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~l1_orders_2(sK1) | ~m1_yellow_0(X0,sK1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,sK3,sK4) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~l1_orders_2(sK1) | ~m1_yellow_0(X0,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f74,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0) | ~m1_yellow_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(u1_orders_2(X0),u1_orders_2(sK1)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,sK3,sK4) | ~m1_subset_1(sK3,u1_struct_0(X0))) )),
% 0.21/0.51    inference(resolution,[],[f67,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(u1_orders_2(sK1))) | ~m1_subset_1(sK3,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,sK3,sK4)) )),
% 0.21/0.51    inference(resolution,[],[f66,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,sK4),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1)))) )),
% 0.21/0.51    inference(global_subsumption,[],[f25,f26,f48,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~r2_hidden(k4_tarski(sK3,sK4),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_orders_2(sK1)))) )),
% 0.21/0.51    inference(resolution,[],[f58,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~r1_orders_2(sK1,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(k4_tarski(X0,X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_orders_2(X1)))) )),
% 0.21/0.51    inference(resolution,[],[f37,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    l1_orders_2(sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f29,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.21/0.51    inference(resolution,[],[f33,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    l1_waybel_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    m1_yellow_0(sK2,sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f29,f28,f51,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~l1_waybel_0(sK1,sK0) | ~l1_waybel_0(sK2,sK0) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f34,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    m1_yellow_6(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_waybel_0(X2,X0) | m1_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    l1_waybel_0(sK2,sK0)),
% 0.21/0.51    inference(global_subsumption,[],[f29,f28,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | l1_waybel_0(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f40,f27])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_waybel_0(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    l1_orders_2(sK2)),
% 0.21/0.51    inference(global_subsumption,[],[f29,f52])).
% 0.21/0.51  % (16700)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (16708)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (16696)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (16701)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (16711)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (16704)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | l1_orders_2(sK2)),
% 0.21/0.52    inference(resolution,[],[f51,f33])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f24,f20])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f19,f21])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16702)------------------------------
% 0.21/0.52  % (16702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16702)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16702)Memory used [KB]: 10746
% 0.21/0.52  % (16702)Time elapsed: 0.097 s
% 0.21/0.52  % (16702)------------------------------
% 0.21/0.52  % (16702)------------------------------
% 0.21/0.52  % (16689)Success in time 0.163 s
%------------------------------------------------------------------------------

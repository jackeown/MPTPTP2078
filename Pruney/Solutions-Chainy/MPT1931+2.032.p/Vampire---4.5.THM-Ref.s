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
% DateTime   : Thu Dec  3 13:22:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 177 expanded)
%              Number of leaves         :    6 (  32 expanded)
%              Depth                    :   22
%              Number of atoms          :  217 ( 952 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

% (22799)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f79,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f77,f19])).

fof(f19,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X5] :
      ( ~ l1_waybel_0(sK1,X5)
      | ~ l1_struct_0(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f76,f18])).

fof(f18,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f75,f17])).

fof(f17,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f73,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v7_waybel_0(sK1)
      | ~ l1_waybel_0(sK1,X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f70,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(f70,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f69,f20])).

fof(f20,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f65,f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X3),X2)),X3)
      | r1_waybel_0(sK0,sK1,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f60,f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | r1_waybel_0(sK0,X0,X1) ) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_0(sK0,sK1,X1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f57,f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ r2_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f56,f19])).

fof(f56,plain,(
    ! [X12,X10,X11] :
      ( ~ l1_waybel_0(X10,sK0)
      | v2_struct_0(X10)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(subsumption_resolution,[],[f51,f21])).

fof(f51,plain,(
    ! [X12,X10,X11] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X10)
      | ~ l1_waybel_0(X10,sK0)
      | ~ m1_subset_1(X11,u1_struct_0(X10))
      | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12)
      | ~ r2_waybel_0(sK0,X10,X12) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1),X0)),u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK1,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_subset_1(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:09:24 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.49  % (22794)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (22814)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (22806)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (22814)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f79,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.20/0.50  % (22799)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f77,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    l1_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X5] : (~l1_waybel_0(sK1,X5) | ~l1_struct_0(X5) | v2_struct_0(X5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f76,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    v7_waybel_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X5] : (~l1_struct_0(X5) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,X5) | v2_struct_0(X5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v4_orders_2(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X5] : (~l1_struct_0(X5) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,X5) | v2_struct_0(X5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f73,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X5] : (~l1_struct_0(X5) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,X5) | v2_struct_0(X5)) )),
% 0.20/0.50    inference(resolution,[],[f70,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(resolution,[],[f65,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X3),X2)),X3) | r1_waybel_0(sK0,sK1,X3) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(resolution,[],[f61,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.20/0.50    inference(definition_unfolding,[],[f36,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f16])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f59,f19])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0),X1)),k6_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.20/0.50    inference(resolution,[],[f58,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f47,f21])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | r1_waybel_0(sK0,X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f22,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r1_waybel_0(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X1) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f16])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~r2_waybel_0(sK0,sK1,X1)) )),
% 0.20/0.50    inference(resolution,[],[f56,f19])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X12,X10,X11] : (~l1_waybel_0(X10,sK0) | v2_struct_0(X10) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f51,f21])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X12,X10,X11] : (v2_struct_0(sK0) | v2_struct_0(X10) | ~l1_waybel_0(X10,sK0) | ~m1_subset_1(X11,u1_struct_0(X10)) | r2_hidden(k2_waybel_0(sK0,X10,sK3(sK0,X10,X12,X11)),X12) | ~r2_waybel_0(sK0,X10,X12)) )),
% 0.20/0.50    inference(resolution,[],[f22,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1),X0)),u1_struct_0(sK0)) | r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.50    inference(resolution,[],[f61,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_subset_1(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.20/0.50    inference(definition_unfolding,[],[f35,f30])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (22814)------------------------------
% 0.20/0.51  % (22814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22814)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (22814)Memory used [KB]: 1791
% 0.20/0.51  % (22814)Time elapsed: 0.053 s
% 0.20/0.51  % (22814)------------------------------
% 0.20/0.51  % (22814)------------------------------
% 0.20/0.51  % (22808)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (22800)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (22796)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (22792)Success in time 0.162 s
%------------------------------------------------------------------------------

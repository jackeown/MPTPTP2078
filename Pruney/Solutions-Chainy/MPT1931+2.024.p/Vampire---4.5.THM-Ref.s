%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:40 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 152 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   22
%              Number of atoms          :  235 ( 678 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f105,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f104,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f101,f87])).

fof(f87,plain,(
    ! [X0] : r2_waybel_0(sK0,sK1,X0) ),
    inference(subsumption_resolution,[],[f86,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f86,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v2_struct_0(sK0)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | v2_struct_0(sK0)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | v2_struct_0(sK0)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ r1_tarski(k1_xboole_0,X0)
      | v2_struct_0(sK0)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ r1_tarski(X2,X3)
      | v2_struct_0(X0)
      | r2_waybel_0(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

% (16612)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f75,plain,(
    r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f31,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    inference(superposition,[],[f68,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f68,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,X0,X1) ) ),
    inference(resolution,[],[f53,f33])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ r2_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f100,f29])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1)
      | ~ r2_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f99,f30])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k2_waybel_0(sK0,X0,sK3(sK0,X0,X2,X1)),X2)
      | ~ r2_waybel_0(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k2_waybel_0(sK0,X0,sK3(sK0,X0,X2,X1)),X2)
      | ~ r2_waybel_0(sK0,X0,X2) ) ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.54  % (16596)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (16613)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (16605)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (16604)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (16597)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (16596)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f110,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(resolution,[],[f105,f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.44/0.55  fof(f105,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.44/0.55    inference(resolution,[],[f104,f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.44/0.55  fof(f104,plain,(
% 1.44/0.55    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 1.44/0.55    inference(resolution,[],[f102,f56])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.44/0.55    inference(resolution,[],[f51,f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    v1_xboole_0(k1_xboole_0)),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    v1_xboole_0(k1_xboole_0)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.44/0.55  fof(f51,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.44/0.55  fof(f102,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f101,f87])).
% 1.44/0.55  fof(f87,plain,(
% 1.44/0.55    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f86,f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ~v2_struct_0(sK0)),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f17])).
% 1.44/0.55  fof(f17,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,plain,(
% 1.44/0.55    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.44/0.55    inference(pure_predicate_removal,[],[f15])).
% 1.44/0.55  fof(f15,plain,(
% 1.44/0.55    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.44/0.55    inference(pure_predicate_removal,[],[f13])).
% 1.44/0.55  fof(f13,negated_conjecture,(
% 1.44/0.55    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.44/0.55    inference(negated_conjecture,[],[f12])).
% 1.44/0.55  fof(f12,conjecture,(
% 1.44/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    ( ! [X0] : (v2_struct_0(sK0) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f85,f58])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.55    inference(resolution,[],[f57,f35])).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(resolution,[],[f56,f48])).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f14])).
% 1.44/0.55  fof(f14,plain,(
% 1.44/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.44/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.55  fof(f85,plain,(
% 1.44/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v2_struct_0(sK0) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f84,f30])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    l1_waybel_0(sK1,sK0)),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f84,plain,(
% 1.44/0.55    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~r1_tarski(k1_xboole_0,X0) | v2_struct_0(sK0) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f83,f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ~v2_struct_0(sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    ( ! [X0] : (v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k1_xboole_0,X0) | v2_struct_0(sK0) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f77,f33])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    l1_struct_0(sK0)),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f77,plain,(
% 1.44/0.55    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~r1_tarski(k1_xboole_0,X0) | v2_struct_0(sK0) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(resolution,[],[f75,f44])).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_waybel_0(X0,X1,X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~r1_tarski(X2,X3) | v2_struct_0(X0) | r2_waybel_0(X0,X1,X3)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f23])).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).
% 1.44/0.55  % (16612)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.55  fof(f75,plain,(
% 1.44/0.55    r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 1.44/0.55    inference(subsumption_resolution,[],[f70,f31])).
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.44/0.55    inference(cnf_transformation,[],[f18])).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 1.44/0.55    inference(superposition,[],[f68,f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.44/0.55  fof(f68,plain,(
% 1.44/0.55    ( ! [X0] : (r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f67,f29])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ( ! [X0] : (v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.44/0.55    inference(resolution,[],[f66,f30])).
% 1.44/0.55  fof(f66,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f65,f32])).
% 1.44/0.55  fof(f65,plain,(
% 1.44/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1)) )),
% 1.44/0.55    inference(resolution,[],[f53,f33])).
% 1.44/0.55  fof(f53,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.44/0.55    inference(definition_unfolding,[],[f37,f47])).
% 1.44/0.55  fof(f47,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,axiom,(
% 1.44/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.44/0.56  fof(f101,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~r2_waybel_0(sK0,sK1,X1)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f100,f29])).
% 1.44/0.56  fof(f100,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,X0)),X1) | ~r2_waybel_0(sK0,sK1,X1)) )),
% 1.44/0.56    inference(resolution,[],[f99,f30])).
% 1.44/0.56  fof(f99,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k2_waybel_0(sK0,X0,sK3(sK0,X0,X2,X1)),X2) | ~r2_waybel_0(sK0,X0,X2)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f98,f32])).
% 1.44/0.56  fof(f98,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k2_waybel_0(sK0,X0,sK3(sK0,X0,X2,X1)),X2) | ~r2_waybel_0(sK0,X0,X2)) )),
% 1.44/0.56    inference(resolution,[],[f42,f33])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~r2_waybel_0(X0,X1,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.44/0.56    inference(flattening,[],[f21])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f9])).
% 1.44/0.56  fof(f9,axiom,(
% 1.44/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (16596)------------------------------
% 1.44/0.56  % (16596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (16596)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (16596)Memory used [KB]: 6268
% 1.44/0.56  % (16596)Time elapsed: 0.112 s
% 1.44/0.56  % (16596)------------------------------
% 1.44/0.56  % (16596)------------------------------
% 1.44/0.56  % (16589)Success in time 0.195 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:22:50 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 722 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   28
%              Number of atoms          :  425 (4565 expanded)
%              Number of equality atoms :   25 (  75 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2076,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2075,f2070])).

fof(f2070,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f1821,f95])).

fof(f95,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f1821,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f43,f1820])).

fof(f1820,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1818,f146])).

fof(f146,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f144,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f144,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f142,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK7(X1,u1_struct_0(sK0)),sK1)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f139,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f139,plain,(
    ! [X6] :
      ( r2_hidden(X6,u1_struct_0(sK0))
      | ~ r2_hidden(X6,sK1) ) ),
    inference(resolution,[],[f81,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1818,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f1812])).

fof(f1812,plain,
    ( sK1 = u1_struct_0(sK0)
    | r1_tarski(u1_struct_0(sK0),sK1)
    | r1_tarski(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f1799,f87])).

fof(f1799,plain,(
    ! [X4] :
      ( r2_hidden(sK7(u1_struct_0(sK0),X4),sK1)
      | sK1 = u1_struct_0(sK0)
      | r1_tarski(u1_struct_0(sK0),X4) ) ),
    inference(subsumption_resolution,[],[f1795,f86])).

fof(f1795,plain,(
    ! [X4] :
      ( r2_hidden(sK7(u1_struct_0(sK0),X4),sK1)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(sK7(u1_struct_0(sK0),X4),u1_struct_0(sK0))
      | r1_tarski(u1_struct_0(sK0),X4) ) ),
    inference(resolution,[],[f1754,f808])).

fof(f808,plain,(
    ! [X2] :
      ( r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),X2))
      | r1_tarski(u1_struct_0(sK0),X2) ) ),
    inference(resolution,[],[f447,f119])).

fof(f119,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f118,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f118,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f116,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f86,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f447,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK5(sK0,X12,sK7(u1_struct_0(sK0),X13)),X12)
      | r2_lattice3(sK0,X12,sK7(u1_struct_0(sK0),X13))
      | r1_tarski(u1_struct_0(sK0),X13) ) ),
    inference(resolution,[],[f378,f86])).

fof(f378,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK0))
      | r2_lattice3(sK0,X4,X5)
      | r2_hidden(sK5(sK0,X4,X5),X4) ) ),
    inference(resolution,[],[f375,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f76,f73])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f375,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(sK5(sK0,X1,X0),X1)
      | r2_lattice3(sK0,X1,X0) ) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1754,plain,(
    ! [X2] :
      ( ~ r2_lattice3(sK0,k1_xboole_0,X2)
      | r2_hidden(X2,sK1)
      | sK1 = u1_struct_0(sK0)
      | ~ r2_hidden(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1751,f96])).

fof(f1751,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f1745,f135])).

fof(f135,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f134,f44])).

fof(f44,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f134,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f1745,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f1732])).

fof(f1732,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f1731,f1565])).

fof(f1565,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f1564,f104])).

fof(f104,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f55,f51])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f1564,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f1563,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1563,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1562,f51])).

fof(f1562,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1561,f50])).

fof(f50,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1561,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
      | ~ v1_yellow_0(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1560,f49])).

fof(f49,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1560,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)
      | ~ v5_orders_2(sK0)
      | ~ v1_yellow_0(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1395,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f1395,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(subsumption_resolution,[],[f1394,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f78,f51])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f1394,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(resolution,[],[f91,f51])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f1731,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f1729,f47])).

fof(f1729,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f1573,f46])).

fof(f46,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1573,plain,(
    ! [X2,X0,X1] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | ~ r1_orders_2(sK0,X1,X2)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1572,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1572,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | ~ r1_orders_2(sK0,X1,X2)
      | r2_hidden(X2,X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f43,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f2075,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f2074,f1820])).

fof(f2074,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1828,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f1828,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f112,f1820])).

fof(f112,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f111,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f109,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:59:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (23785)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (23762)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (23774)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (23764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (23766)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (23761)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.50  % (23763)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (23784)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (23782)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (23760)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (23771)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (23775)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (23785)Refutation not found, incomplete strategy% (23785)------------------------------
% 0.19/0.52  % (23785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (23785)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (23785)Memory used [KB]: 11001
% 0.19/0.52  % (23785)Time elapsed: 0.083 s
% 0.19/0.52  % (23785)------------------------------
% 0.19/0.52  % (23785)------------------------------
% 0.19/0.52  % (23767)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (23780)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (23777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (23772)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (23765)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (23788)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (23783)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (23779)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (23790)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (23776)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (23786)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (23768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (23769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.54  % (23789)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.54  % (23787)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.54  % (23791)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (23781)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.55  % (23792)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.23/0.67  % (23834)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.67  % (23766)Refutation found. Thanks to Tanya!
% 2.23/0.67  % SZS status Theorem for theBenchmark
% 2.23/0.67  % SZS output start Proof for theBenchmark
% 2.23/0.67  fof(f2076,plain,(
% 2.23/0.67    $false),
% 2.23/0.67    inference(subsumption_resolution,[],[f2075,f2070])).
% 2.23/0.68  fof(f2070,plain,(
% 2.23/0.68    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1821,f95])).
% 2.23/0.68  fof(f95,plain,(
% 2.23/0.68    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 2.23/0.68    inference(backward_demodulation,[],[f53,f54])).
% 2.23/0.68  fof(f54,plain,(
% 2.23/0.68    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.23/0.68    inference(cnf_transformation,[],[f6])).
% 2.23/0.68  fof(f6,axiom,(
% 2.23/0.68    ! [X0] : k2_subset_1(X0) = X0),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.23/0.68  fof(f53,plain,(
% 2.23/0.68    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f8])).
% 2.23/0.68  fof(f8,axiom,(
% 2.23/0.68    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 2.23/0.68  fof(f1821,plain,(
% 2.23/0.68    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.68    inference(backward_demodulation,[],[f43,f1820])).
% 2.23/0.68  fof(f1820,plain,(
% 2.23/0.68    sK1 = u1_struct_0(sK0)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1818,f146])).
% 2.23/0.68  fof(f146,plain,(
% 2.23/0.68    ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 2.23/0.68    inference(resolution,[],[f144,f84])).
% 2.23/0.68  fof(f84,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.23/0.68    inference(cnf_transformation,[],[f4])).
% 2.23/0.68  fof(f4,axiom,(
% 2.23/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.23/0.68  fof(f144,plain,(
% 2.23/0.68    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.23/0.68    inference(duplicate_literal_removal,[],[f143])).
% 2.23/0.68  fof(f143,plain,(
% 2.23/0.68    r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,u1_struct_0(sK0))),
% 2.23/0.68    inference(resolution,[],[f142,f86])).
% 2.23/0.68  fof(f86,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f39])).
% 2.23/0.68  fof(f39,plain,(
% 2.23/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f2])).
% 2.23/0.68  fof(f2,axiom,(
% 2.23/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.23/0.68  fof(f142,plain,(
% 2.23/0.68    ( ! [X1] : (~r2_hidden(sK7(X1,u1_struct_0(sK0)),sK1) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 2.23/0.68    inference(resolution,[],[f139,f87])).
% 2.23/0.68  fof(f87,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f39])).
% 2.23/0.68  fof(f139,plain,(
% 2.23/0.68    ( ! [X6] : (r2_hidden(X6,u1_struct_0(sK0)) | ~r2_hidden(X6,sK1)) )),
% 2.23/0.68    inference(resolution,[],[f81,f47])).
% 2.23/0.68  fof(f47,plain,(
% 2.23/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f25,plain,(
% 2.23/0.68    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f24])).
% 2.23/0.68  fof(f24,plain,(
% 2.23/0.68    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f22])).
% 2.23/0.68  fof(f22,plain,(
% 2.23/0.68    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.68    inference(pure_predicate_removal,[],[f21])).
% 2.23/0.68  fof(f21,plain,(
% 2.23/0.68    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.68    inference(pure_predicate_removal,[],[f20])).
% 2.23/0.68  fof(f20,plain,(
% 2.23/0.68    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.68    inference(pure_predicate_removal,[],[f19])).
% 2.23/0.68  fof(f19,negated_conjecture,(
% 2.23/0.68    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.68    inference(negated_conjecture,[],[f18])).
% 2.23/0.68  fof(f18,conjecture,(
% 2.23/0.68    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 2.23/0.68  fof(f81,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f38])).
% 2.23/0.68  fof(f38,plain,(
% 2.23/0.68    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f7])).
% 2.23/0.68  fof(f7,axiom,(
% 2.23/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.23/0.68  fof(f1818,plain,(
% 2.23/0.68    sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),sK1)),
% 2.23/0.68    inference(duplicate_literal_removal,[],[f1812])).
% 2.23/0.68  fof(f1812,plain,(
% 2.23/0.68    sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),sK1) | r1_tarski(u1_struct_0(sK0),sK1)),
% 2.23/0.68    inference(resolution,[],[f1799,f87])).
% 2.23/0.68  fof(f1799,plain,(
% 2.23/0.68    ( ! [X4] : (r2_hidden(sK7(u1_struct_0(sK0),X4),sK1) | sK1 = u1_struct_0(sK0) | r1_tarski(u1_struct_0(sK0),X4)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1795,f86])).
% 2.23/0.68  fof(f1795,plain,(
% 2.23/0.68    ( ! [X4] : (r2_hidden(sK7(u1_struct_0(sK0),X4),sK1) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK7(u1_struct_0(sK0),X4),u1_struct_0(sK0)) | r1_tarski(u1_struct_0(sK0),X4)) )),
% 2.23/0.68    inference(resolution,[],[f1754,f808])).
% 2.23/0.68  fof(f808,plain,(
% 2.23/0.68    ( ! [X2] : (r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0),X2)) | r1_tarski(u1_struct_0(sK0),X2)) )),
% 2.23/0.68    inference(resolution,[],[f447,f119])).
% 2.23/0.68  fof(f119,plain,(
% 2.23/0.68    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.23/0.68    inference(resolution,[],[f118,f88])).
% 2.23/0.68  fof(f88,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f40])).
% 2.23/0.68  fof(f40,plain,(
% 2.23/0.68    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.23/0.68    inference(ennf_transformation,[],[f10])).
% 2.23/0.68  fof(f10,axiom,(
% 2.23/0.68    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.23/0.68  fof(f118,plain,(
% 2.23/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.23/0.68    inference(resolution,[],[f116,f52])).
% 2.23/0.68  fof(f52,plain,(
% 2.23/0.68    v1_xboole_0(k1_xboole_0)),
% 2.23/0.68    inference(cnf_transformation,[],[f3])).
% 2.23/0.68  fof(f3,axiom,(
% 2.23/0.68    v1_xboole_0(k1_xboole_0)),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.23/0.68  fof(f116,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 2.23/0.68    inference(resolution,[],[f86,f73])).
% 2.23/0.68  fof(f73,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f1])).
% 2.23/0.68  fof(f1,axiom,(
% 2.23/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.23/0.68  fof(f447,plain,(
% 2.23/0.68    ( ! [X12,X13] : (r2_hidden(sK5(sK0,X12,sK7(u1_struct_0(sK0),X13)),X12) | r2_lattice3(sK0,X12,sK7(u1_struct_0(sK0),X13)) | r1_tarski(u1_struct_0(sK0),X13)) )),
% 2.23/0.68    inference(resolution,[],[f378,f86])).
% 2.23/0.68  fof(f378,plain,(
% 2.23/0.68    ( ! [X4,X5] : (~r2_hidden(X5,u1_struct_0(sK0)) | r2_lattice3(sK0,X4,X5) | r2_hidden(sK5(sK0,X4,X5),X4)) )),
% 2.23/0.68    inference(resolution,[],[f375,f96])).
% 2.23/0.68  fof(f96,plain,(
% 2.23/0.68    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f76,f73])).
% 2.23/0.68  fof(f76,plain,(
% 2.23/0.68    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f35])).
% 2.23/0.68  fof(f35,plain,(
% 2.23/0.68    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f5])).
% 2.23/0.68  fof(f5,axiom,(
% 2.23/0.68    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.23/0.68  fof(f375,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK5(sK0,X1,X0),X1) | r2_lattice3(sK0,X1,X0)) )),
% 2.23/0.68    inference(resolution,[],[f69,f51])).
% 2.23/0.68  fof(f51,plain,(
% 2.23/0.68    l1_orders_2(sK0)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f69,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f32])).
% 2.23/0.68  fof(f32,plain,(
% 2.23/0.68    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(flattening,[],[f31])).
% 2.23/0.68  fof(f31,plain,(
% 2.23/0.68    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f11])).
% 2.23/0.68  fof(f11,axiom,(
% 2.23/0.68    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 2.23/0.68  fof(f1754,plain,(
% 2.23/0.68    ( ! [X2] : (~r2_lattice3(sK0,k1_xboole_0,X2) | r2_hidden(X2,sK1) | sK1 = u1_struct_0(sK0) | ~r2_hidden(X2,u1_struct_0(sK0))) )),
% 2.23/0.68    inference(resolution,[],[f1751,f96])).
% 2.23/0.68  fof(f1751,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0) | sK1 = u1_struct_0(sK0)) )),
% 2.23/0.68    inference(resolution,[],[f1745,f135])).
% 2.23/0.68  fof(f135,plain,(
% 2.23/0.68    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 2.23/0.68    inference(resolution,[],[f134,f44])).
% 2.23/0.68  fof(f44,plain,(
% 2.23/0.68    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f134,plain,(
% 2.23/0.68    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 2.23/0.68    inference(resolution,[],[f79,f47])).
% 2.23/0.68  fof(f79,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f37])).
% 2.23/0.68  fof(f37,plain,(
% 2.23/0.68    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f17])).
% 2.23/0.68  fof(f17,axiom,(
% 2.23/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 2.23/0.68  fof(f1745,plain,(
% 2.23/0.68    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0)) )),
% 2.23/0.68    inference(duplicate_literal_removal,[],[f1732])).
% 2.23/0.68  fof(f1732,plain,(
% 2.23/0.68    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0)) )),
% 2.23/0.68    inference(resolution,[],[f1731,f1565])).
% 2.23/0.68  fof(f1565,plain,(
% 2.23/0.68    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0)) )),
% 2.23/0.68    inference(forward_demodulation,[],[f1564,f104])).
% 2.23/0.68  fof(f104,plain,(
% 2.23/0.68    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 2.23/0.68    inference(resolution,[],[f55,f51])).
% 2.23/0.68  fof(f55,plain,(
% 2.23/0.68    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f26])).
% 2.23/0.68  fof(f26,plain,(
% 2.23/0.68    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f12])).
% 2.23/0.68  fof(f12,axiom,(
% 2.23/0.68    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 2.23/0.68  fof(f1564,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1563,f48])).
% 2.23/0.68  fof(f48,plain,(
% 2.23/0.68    ~v2_struct_0(sK0)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f1563,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | v2_struct_0(sK0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1562,f51])).
% 2.23/0.68  fof(f1562,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1561,f50])).
% 2.23/0.68  fof(f50,plain,(
% 2.23/0.68    v1_yellow_0(sK0)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f1561,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1560,f49])).
% 2.23/0.68  fof(f49,plain,(
% 2.23/0.68    v5_orders_2(sK0)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f1560,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 2.23/0.68    inference(resolution,[],[f1395,f71])).
% 2.23/0.68  fof(f71,plain,(
% 2.23/0.68    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f34])).
% 2.23/0.68  fof(f34,plain,(
% 2.23/0.68    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f33])).
% 2.23/0.68  fof(f33,plain,(
% 2.23/0.68    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f23])).
% 2.23/0.68  fof(f23,plain,(
% 2.23/0.68    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 2.23/0.68    inference(pure_predicate_removal,[],[f15])).
% 2.23/0.68  fof(f15,axiom,(
% 2.23/0.68    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 2.23/0.68  fof(f1395,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1394,f109])).
% 2.23/0.68  fof(f109,plain,(
% 2.23/0.68    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 2.23/0.68    inference(resolution,[],[f78,f51])).
% 2.23/0.68  fof(f78,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 2.23/0.68    inference(cnf_transformation,[],[f36])).
% 2.23/0.68  fof(f36,plain,(
% 2.23/0.68    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f14])).
% 2.23/0.68  fof(f14,axiom,(
% 2.23/0.68    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 2.23/0.68  fof(f1394,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 2.23/0.68    inference(resolution,[],[f91,f51])).
% 2.23/0.68  fof(f91,plain,(
% 2.23/0.68    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 2.23/0.68    inference(equality_resolution,[],[f65])).
% 2.23/0.68  fof(f65,plain,(
% 2.23/0.68    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 2.23/0.68    inference(cnf_transformation,[],[f30])).
% 2.23/0.68  fof(f30,plain,(
% 2.23/0.68    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(flattening,[],[f29])).
% 2.23/0.68  fof(f29,plain,(
% 2.23/0.68    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f13])).
% 2.23/0.68  fof(f13,axiom,(
% 2.23/0.68    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 2.23/0.68  fof(f1731,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,X0) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1729,f47])).
% 2.23/0.68  fof(f1729,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X1,X0) | r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.23/0.68    inference(resolution,[],[f1573,f46])).
% 2.23/0.68  fof(f46,plain,(
% 2.23/0.68    v13_waybel_0(sK1,sK0)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f1573,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~v13_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~r1_orders_2(sK0,X1,X2) | r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f1572,f89])).
% 2.23/0.68  fof(f89,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f42])).
% 2.23/0.68  fof(f42,plain,(
% 2.23/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.23/0.68    inference(flattening,[],[f41])).
% 2.23/0.68  fof(f41,plain,(
% 2.23/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.23/0.68    inference(ennf_transformation,[],[f9])).
% 2.23/0.68  fof(f9,axiom,(
% 2.23/0.68    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.23/0.68  fof(f1572,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~r1_orders_2(sK0,X1,X2) | r2_hidden(X2,X0) | ~v13_waybel_0(X0,sK0)) )),
% 2.23/0.68    inference(resolution,[],[f60,f51])).
% 2.23/0.68  fof(f60,plain,(
% 2.23/0.68    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f28])).
% 2.23/0.68  fof(f28,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(flattening,[],[f27])).
% 2.23/0.68  fof(f27,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f16])).
% 2.23/0.68  fof(f16,axiom,(
% 2.23/0.68    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 2.23/0.68  fof(f43,plain,(
% 2.23/0.68    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f2075,plain,(
% 2.23/0.68    r2_hidden(k3_yellow_0(sK0),sK1)),
% 2.23/0.68    inference(forward_demodulation,[],[f2074,f1820])).
% 2.23/0.68  fof(f2074,plain,(
% 2.23/0.68    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 2.23/0.68    inference(subsumption_resolution,[],[f1828,f45])).
% 2.23/0.68  fof(f45,plain,(
% 2.23/0.68    ~v1_xboole_0(sK1)),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f1828,plain,(
% 2.23/0.68    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 2.23/0.68    inference(backward_demodulation,[],[f112,f1820])).
% 2.23/0.68  fof(f112,plain,(
% 2.23/0.68    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 2.23/0.68    inference(resolution,[],[f111,f77])).
% 2.23/0.68  fof(f77,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f35])).
% 2.23/0.68  fof(f111,plain,(
% 2.23/0.68    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 2.23/0.68    inference(superposition,[],[f109,f104])).
% 2.23/0.68  % SZS output end Proof for theBenchmark
% 2.23/0.68  % (23766)------------------------------
% 2.23/0.68  % (23766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.68  % (23766)Termination reason: Refutation
% 2.23/0.68  
% 2.23/0.68  % (23766)Memory used [KB]: 8187
% 2.23/0.68  % (23766)Time elapsed: 0.255 s
% 2.23/0.68  % (23766)------------------------------
% 2.23/0.68  % (23766)------------------------------
% 2.23/0.69  % (23754)Success in time 0.333 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:52 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  131 (1183 expanded)
%              Number of leaves         :   17 ( 240 expanded)
%              Depth                    :   30
%              Number of atoms          :  452 (7455 expanded)
%              Number of equality atoms :   46 ( 169 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f587,plain,(
    $false ),
    inference(subsumption_resolution,[],[f586,f421])).

fof(f421,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f43,f418])).

fof(f418,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f416,f166])).

fof(f166,plain,(
    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f162,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f162,plain,(
    r2_hidden(k2_subset_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f123,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f123,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f117,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f117,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f40,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f416,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f415,f122])).

fof(f122,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f117,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f415,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f411,f346])).

fof(f346,plain,
    ( m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f345,f183])).

fof(f183,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK0))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f181,f75])).

fof(f181,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f178,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f178,plain,(
    r2_hidden(sK6(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f171,f99])).

fof(f99,plain,(
    r2_hidden(sK6(sK1),sK1) ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f167,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f167,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f163,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f163,plain,(
    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f123,f43])).

fof(f345,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f343,f166])).

fof(f343,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f337,f122])).

fof(f337,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(factoring,[],[f330])).

fof(f330,plain,(
    ! [X0] :
      ( r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f179,f43])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,sK1),X1)
      | sK1 = X1 ) ),
    inference(resolution,[],[f171,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f411,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f402,f184])).

fof(f184,plain,(
    ! [X2] :
      ( r2_hidden(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f181,f76])).

fof(f402,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = u1_struct_0(sK0)
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f399,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f399,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f269,f43])).

fof(f269,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X5))
      | ~ m1_subset_1(sK7(X5,X6,sK1),u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(sK7(X5,X6,sK1),X6)
      | sK1 = X6 ) ),
    inference(resolution,[],[f264,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f264,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f263,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f263,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | r2_hidden(X2,sK1)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f259,f72])).

fof(f259,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0)
      | r2_hidden(sK5(sK0,k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f255,f111])).

fof(f111,plain,(
    ! [X14,X13] :
      ( r2_lattice3(sK0,X14,X13)
      | r2_hidden(sK5(sK0,X14,X13),X14)
      | ~ m1_subset_1(X13,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f253,f147])).

fof(f147,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f43])).

fof(f146,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f39,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f39,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f253,plain,(
    ! [X4] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,X4) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X4] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X4) ) ),
    inference(resolution,[],[f249,f233])).

fof(f233,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f232,f103])).

fof(f103,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,k1_xboole_0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f139,f125])).

fof(f125,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f102,f49])).

fof(f102,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f101,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f48,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) ) ),
    inference(resolution,[],[f113,f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f113,plain,(
    ! [X17] : m1_subset_1(k1_yellow_0(sK0,X17),u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f244,f43])).

fof(f244,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f114,f42])).

fof(f42,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X4,X3)
      | ~ r1_orders_2(sK0,X4,X5)
      | r2_hidden(X5,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X4,X3)
      | ~ r1_orders_2(sK0,X4,X5)
      | r2_hidden(X5,X3)
      | ~ v13_waybel_0(X3,sK0) ) ),
    inference(resolution,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f586,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f585,f93])).

fof(f93,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f585,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f419,f579])).

fof(f579,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f437,f98])).

fof(f98,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f40,f76])).

fof(f437,plain,(
    m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f138,f418])).

fof(f138,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f113,f103])).

fof(f419,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f38,f418])).

fof(f38,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (818970625)
% 0.13/0.37  ipcrm: permission denied for id (819101701)
% 0.13/0.37  ipcrm: permission denied for id (819134470)
% 0.13/0.37  ipcrm: permission denied for id (819200007)
% 0.13/0.38  ipcrm: permission denied for id (819331084)
% 0.13/0.38  ipcrm: permission denied for id (819429393)
% 0.13/0.38  ipcrm: permission denied for id (819462162)
% 0.13/0.39  ipcrm: permission denied for id (819494931)
% 0.21/0.39  ipcrm: permission denied for id (819724313)
% 0.21/0.39  ipcrm: permission denied for id (819757082)
% 0.21/0.40  ipcrm: permission denied for id (819822623)
% 0.21/0.41  ipcrm: permission denied for id (819953700)
% 0.21/0.41  ipcrm: permission denied for id (820019238)
% 0.21/0.41  ipcrm: permission denied for id (820052008)
% 0.21/0.42  ipcrm: permission denied for id (820150317)
% 0.21/0.42  ipcrm: permission denied for id (820183086)
% 0.21/0.42  ipcrm: permission denied for id (820281394)
% 0.21/0.43  ipcrm: permission denied for id (820346934)
% 0.21/0.43  ipcrm: permission denied for id (820412473)
% 0.21/0.43  ipcrm: permission denied for id (820445242)
% 0.21/0.43  ipcrm: permission denied for id (820478011)
% 0.21/0.43  ipcrm: permission denied for id (820543549)
% 0.21/0.44  ipcrm: permission denied for id (820576319)
% 0.21/0.44  ipcrm: permission denied for id (820674627)
% 0.21/0.44  ipcrm: permission denied for id (820707396)
% 0.21/0.45  ipcrm: permission denied for id (820805707)
% 0.21/0.45  ipcrm: permission denied for id (820838477)
% 0.21/0.46  ipcrm: permission denied for id (820936784)
% 0.21/0.46  ipcrm: permission denied for id (820969553)
% 0.21/0.46  ipcrm: permission denied for id (821002323)
% 0.21/0.46  ipcrm: permission denied for id (821035092)
% 0.21/0.47  ipcrm: permission denied for id (821166171)
% 0.21/0.47  ipcrm: permission denied for id (821231709)
% 0.21/0.48  ipcrm: permission denied for id (821297250)
% 0.21/0.48  ipcrm: permission denied for id (821362791)
% 0.21/0.49  ipcrm: permission denied for id (821395561)
% 0.21/0.49  ipcrm: permission denied for id (821428331)
% 0.21/0.49  ipcrm: permission denied for id (821461100)
% 0.21/0.49  ipcrm: permission denied for id (821526638)
% 0.21/0.49  ipcrm: permission denied for id (821559407)
% 0.21/0.50  ipcrm: permission denied for id (821657715)
% 0.21/0.50  ipcrm: permission denied for id (821723253)
% 0.21/0.51  ipcrm: permission denied for id (821788792)
% 0.21/0.51  ipcrm: permission denied for id (821821561)
% 0.21/0.51  ipcrm: permission denied for id (821887101)
% 0.21/0.51  ipcrm: permission denied for id (821952639)
% 0.37/0.64  % (19529)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.37/0.64  % (19527)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.65  % (19552)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.37/0.65  % (19542)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.37/0.66  % (19534)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.37/0.66  % (19550)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.37/0.66  % (19536)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.37/0.67  % (19525)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.37/0.68  % (19528)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.37/0.68  % (19541)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.37/0.68  % (19537)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.37/0.68  % (19533)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.37/0.68  % (19540)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.37/0.68  % (19526)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.37/0.69  % (19538)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.37/0.69  % (19532)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.37/0.69  % (19547)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.37/0.69  % (19548)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.37/0.69  % (19551)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.37/0.70  % (19530)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.37/0.70  % (19546)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.37/0.70  % (19539)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.37/0.70  % (19544)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.37/0.70  % (19531)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.37/0.71  % (19543)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.37/0.71  % (19554)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.37/0.71  % (19549)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.37/0.71  % (19553)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.37/0.71  % (19535)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.37/0.72  % (19545)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.37/0.73  % (19547)Refutation not found, incomplete strategy% (19547)------------------------------
% 0.37/0.73  % (19547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.73  % (19547)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.73  
% 0.37/0.73  % (19547)Memory used [KB]: 11129
% 0.37/0.73  % (19547)Time elapsed: 0.109 s
% 0.37/0.73  % (19547)------------------------------
% 0.37/0.73  % (19547)------------------------------
% 0.37/0.75  % (19551)Refutation not found, incomplete strategy% (19551)------------------------------
% 0.37/0.75  % (19551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.75  % (19551)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.75  
% 0.37/0.75  % (19551)Memory used [KB]: 11001
% 0.37/0.75  % (19551)Time elapsed: 0.187 s
% 0.37/0.75  % (19551)------------------------------
% 0.37/0.75  % (19551)------------------------------
% 0.49/0.76  % (19546)Refutation found. Thanks to Tanya!
% 0.49/0.76  % SZS status Theorem for theBenchmark
% 0.49/0.77  % SZS output start Proof for theBenchmark
% 0.49/0.77  fof(f587,plain,(
% 0.49/0.77    $false),
% 0.49/0.77    inference(subsumption_resolution,[],[f586,f421])).
% 0.49/0.77  fof(f421,plain,(
% 0.49/0.77    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.49/0.77    inference(backward_demodulation,[],[f43,f418])).
% 0.49/0.77  fof(f418,plain,(
% 0.49/0.77    sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f416,f166])).
% 0.49/0.77  fof(f166,plain,(
% 0.49/0.77    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(forward_demodulation,[],[f162,f51])).
% 0.49/0.77  fof(f51,plain,(
% 0.49/0.77    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.49/0.77    inference(cnf_transformation,[],[f6])).
% 0.49/0.77  fof(f6,axiom,(
% 0.49/0.77    ! [X0] : k2_subset_1(X0) = X0),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.49/0.77  fof(f162,plain,(
% 0.49/0.77    r2_hidden(k2_subset_1(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f123,f52])).
% 0.49/0.77  fof(f52,plain,(
% 0.49/0.77    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.49/0.77    inference(cnf_transformation,[],[f7])).
% 0.49/0.77  fof(f7,axiom,(
% 0.49/0.77    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.49/0.77  fof(f123,plain,(
% 0.49/0.77    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.49/0.77    inference(resolution,[],[f117,f76])).
% 0.49/0.77  fof(f76,plain,(
% 0.49/0.77    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f30])).
% 0.49/0.77  fof(f30,plain,(
% 0.49/0.77    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f5])).
% 0.49/0.77  fof(f5,axiom,(
% 0.49/0.77    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.49/0.77  fof(f117,plain,(
% 0.49/0.77    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f96,f43])).
% 0.49/0.77  fof(f96,plain,(
% 0.49/0.77    ( ! [X0] : (~m1_subset_1(sK1,X0) | ~v1_xboole_0(X0)) )),
% 0.49/0.77    inference(resolution,[],[f40,f74])).
% 0.49/0.77  fof(f74,plain,(
% 0.49/0.77    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f30])).
% 0.49/0.77  fof(f40,plain,(
% 0.49/0.77    ~v1_xboole_0(sK1)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f20,plain,(
% 0.49/0.77    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.49/0.77    inference(flattening,[],[f19])).
% 0.49/0.77  fof(f19,plain,(
% 0.49/0.77    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f18])).
% 0.49/0.77  fof(f18,negated_conjecture,(
% 0.49/0.77    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.49/0.77    inference(negated_conjecture,[],[f17])).
% 0.49/0.77  fof(f17,conjecture,(
% 0.49/0.77    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.49/0.77  fof(f416,plain,(
% 0.49/0.77    sK1 = u1_struct_0(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f415,f122])).
% 0.49/0.77  fof(f122,plain,(
% 0.49/0.77    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.49/0.77    inference(resolution,[],[f117,f75])).
% 0.49/0.77  fof(f75,plain,(
% 0.49/0.77    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f30])).
% 0.49/0.77  fof(f415,plain,(
% 0.49/0.77    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f411,f346])).
% 0.49/0.77  fof(f346,plain,(
% 0.49/0.77    m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(resolution,[],[f345,f183])).
% 0.49/0.77  fof(f183,plain,(
% 0.49/0.77    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK0)) | m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f181,f75])).
% 0.49/0.77  fof(f181,plain,(
% 0.49/0.77    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.49/0.77    inference(resolution,[],[f178,f72])).
% 0.49/0.77  fof(f72,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f1])).
% 0.49/0.77  fof(f1,axiom,(
% 0.49/0.77    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.49/0.77  fof(f178,plain,(
% 0.49/0.77    r2_hidden(sK6(sK1),u1_struct_0(sK0))),
% 0.49/0.77    inference(resolution,[],[f171,f99])).
% 0.49/0.77  fof(f99,plain,(
% 0.49/0.77    r2_hidden(sK6(sK1),sK1)),
% 0.49/0.77    inference(resolution,[],[f40,f71])).
% 0.49/0.77  fof(f71,plain,(
% 0.49/0.77    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f1])).
% 0.49/0.77  fof(f171,plain,(
% 0.49/0.77    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f167,f83])).
% 0.49/0.77  fof(f83,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f35])).
% 0.49/0.77  fof(f35,plain,(
% 0.49/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f2])).
% 0.49/0.77  fof(f2,axiom,(
% 0.49/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.49/0.77  fof(f167,plain,(
% 0.49/0.77    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.49/0.77    inference(resolution,[],[f163,f94])).
% 0.49/0.77  fof(f94,plain,(
% 0.49/0.77    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.49/0.77    inference(equality_resolution,[],[f87])).
% 0.49/0.77  fof(f87,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.49/0.77    inference(cnf_transformation,[],[f4])).
% 0.49/0.77  fof(f4,axiom,(
% 0.49/0.77    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.49/0.77  fof(f163,plain,(
% 0.49/0.77    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f123,f43])).
% 0.49/0.77  fof(f345,plain,(
% 0.49/0.77    r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f343,f166])).
% 0.49/0.77  fof(f343,plain,(
% 0.49/0.77    r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f337,f122])).
% 0.49/0.77  fof(f337,plain,(
% 0.49/0.77    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(factoring,[],[f330])).
% 0.49/0.77  fof(f330,plain,(
% 0.49/0.77    ( ! [X0] : (r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0) )),
% 0.49/0.77    inference(resolution,[],[f179,f43])).
% 0.49/0.77  fof(f179,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r2_hidden(sK7(X0,X1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK7(X0,X1,sK1),X1) | sK1 = X1) )),
% 0.49/0.77    inference(resolution,[],[f171,f80])).
% 0.49/0.77  fof(f80,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK7(X0,X1,X2),X1) | X1 = X2) )),
% 0.49/0.77    inference(cnf_transformation,[],[f34])).
% 0.49/0.77  fof(f34,plain,(
% 0.49/0.77    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.49/0.77    inference(flattening,[],[f33])).
% 0.49/0.77  fof(f33,plain,(
% 0.49/0.77    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f8])).
% 0.49/0.77  fof(f8,axiom,(
% 0.49/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.49/0.77  fof(f411,plain,(
% 0.49/0.77    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.49/0.77    inference(duplicate_literal_removal,[],[f408])).
% 0.49/0.77  fof(f408,plain,(
% 0.49/0.77    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK7(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.49/0.77    inference(resolution,[],[f402,f184])).
% 0.49/0.77  fof(f184,plain,(
% 0.49/0.77    ( ! [X2] : (r2_hidden(X2,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f181,f76])).
% 0.49/0.77  fof(f402,plain,(
% 0.49/0.77    ( ! [X0] : (~r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | sK1 = X0) )),
% 0.49/0.77    inference(subsumption_resolution,[],[f399,f90])).
% 0.49/0.77  fof(f90,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f37])).
% 0.49/0.77  fof(f37,plain,(
% 0.49/0.77    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.49/0.77    inference(flattening,[],[f36])).
% 0.49/0.77  fof(f36,plain,(
% 0.49/0.77    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.49/0.77    inference(ennf_transformation,[],[f9])).
% 0.49/0.77  fof(f9,axiom,(
% 0.49/0.77    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.49/0.77  fof(f399,plain,(
% 0.49/0.77    ( ! [X0] : (~m1_subset_1(sK7(u1_struct_0(sK0),X0,sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK7(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0) )),
% 0.49/0.77    inference(resolution,[],[f269,f43])).
% 0.49/0.77  fof(f269,plain,(
% 0.49/0.77    ( ! [X6,X5] : (~m1_subset_1(sK1,k1_zfmisc_1(X5)) | ~m1_subset_1(sK7(X5,X6,sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(X5)) | ~r2_hidden(sK7(X5,X6,sK1),X6) | sK1 = X6) )),
% 0.49/0.77    inference(resolution,[],[f264,f81])).
% 0.49/0.77  fof(f81,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK7(X0,X1,X2),X1) | X1 = X2) )),
% 0.49/0.77    inference(cnf_transformation,[],[f34])).
% 0.49/0.77  fof(f264,plain,(
% 0.49/0.77    ( ! [X2] : (r2_hidden(X2,sK1) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(subsumption_resolution,[],[f263,f50])).
% 0.49/0.77  fof(f50,plain,(
% 0.49/0.77    v1_xboole_0(k1_xboole_0)),
% 0.49/0.77    inference(cnf_transformation,[],[f3])).
% 0.49/0.77  fof(f3,axiom,(
% 0.49/0.77    v1_xboole_0(k1_xboole_0)),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.49/0.77  fof(f263,plain,(
% 0.49/0.77    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | r2_hidden(X2,sK1) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.49/0.77    inference(resolution,[],[f259,f72])).
% 0.49/0.77  fof(f259,plain,(
% 0.49/0.77    ( ! [X0] : (r2_hidden(sK5(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | r2_hidden(X0,sK1)) )),
% 0.49/0.77    inference(duplicate_literal_removal,[],[f257])).
% 0.49/0.77  fof(f257,plain,(
% 0.49/0.77    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | r2_hidden(sK5(sK0,k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f255,f111])).
% 0.49/0.77  fof(f111,plain,(
% 0.49/0.77    ( ! [X14,X13] : (r2_lattice3(sK0,X14,X13) | r2_hidden(sK5(sK0,X14,X13),X14) | ~m1_subset_1(X13,u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f49,f67])).
% 0.49/0.77  fof(f67,plain,(
% 0.49/0.77    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f27])).
% 0.49/0.77  fof(f27,plain,(
% 0.49/0.77    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(flattening,[],[f26])).
% 0.49/0.77  fof(f26,plain,(
% 0.49/0.77    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(ennf_transformation,[],[f10])).
% 0.49/0.77  fof(f10,axiom,(
% 0.49/0.77    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.49/0.77  fof(f49,plain,(
% 0.49/0.77    l1_orders_2(sK0)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f255,plain,(
% 0.49/0.77    ( ! [X0] : (~r2_lattice3(sK0,k1_xboole_0,X0) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)) )),
% 0.49/0.77    inference(resolution,[],[f253,f147])).
% 0.49/0.77  fof(f147,plain,(
% 0.49/0.77    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f146,f43])).
% 0.49/0.77  fof(f146,plain,(
% 0.49/0.77    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(resolution,[],[f39,f78])).
% 0.49/0.77  fof(f78,plain,(
% 0.49/0.77    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.49/0.77    inference(cnf_transformation,[],[f32])).
% 0.49/0.77  fof(f32,plain,(
% 0.49/0.77    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f16])).
% 0.49/0.77  fof(f16,axiom,(
% 0.49/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.49/0.77  fof(f39,plain,(
% 0.49/0.77    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f253,plain,(
% 0.49/0.77    ( ! [X4] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X4)) )),
% 0.49/0.77    inference(duplicate_literal_removal,[],[f252])).
% 0.49/0.77  fof(f252,plain,(
% 0.49/0.77    ( ! [X4] : (~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X4)) )),
% 0.49/0.77    inference(resolution,[],[f249,f233])).
% 0.49/0.77  fof(f233,plain,(
% 0.49/0.77    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0)) )),
% 0.49/0.77    inference(forward_demodulation,[],[f232,f103])).
% 0.49/0.77  fof(f103,plain,(
% 0.49/0.77    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.49/0.77    inference(resolution,[],[f49,f53])).
% 0.49/0.77  fof(f53,plain,(
% 0.49/0.77    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f21])).
% 0.49/0.77  fof(f21,plain,(
% 0.49/0.77    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(ennf_transformation,[],[f11])).
% 0.49/0.77  fof(f11,axiom,(
% 0.49/0.77    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.49/0.77  fof(f232,plain,(
% 0.49/0.77    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),X0)) )),
% 0.49/0.77    inference(resolution,[],[f139,f125])).
% 0.49/0.77  fof(f125,plain,(
% 0.49/0.77    r1_yellow_0(sK0,k1_xboole_0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f102,f49])).
% 0.49/0.77  fof(f102,plain,(
% 0.49/0.77    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f101,f44])).
% 0.49/0.77  fof(f44,plain,(
% 0.49/0.77    ~v2_struct_0(sK0)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f101,plain,(
% 0.49/0.77    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.49/0.77    inference(subsumption_resolution,[],[f100,f47])).
% 0.49/0.77  fof(f47,plain,(
% 0.49/0.77    v5_orders_2(sK0)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f100,plain,(
% 0.49/0.77    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.49/0.77    inference(resolution,[],[f48,f69])).
% 0.49/0.77  fof(f69,plain,(
% 0.49/0.77    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f29])).
% 0.49/0.77  fof(f29,plain,(
% 0.49/0.77    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.49/0.77    inference(flattening,[],[f28])).
% 0.49/0.77  fof(f28,plain,(
% 0.49/0.77    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.49/0.77    inference(ennf_transformation,[],[f14])).
% 0.49/0.77  fof(f14,axiom,(
% 0.49/0.77    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.49/0.77  fof(f48,plain,(
% 0.49/0.77    v1_yellow_0(sK0)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f139,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 0.49/0.77    inference(subsumption_resolution,[],[f136,f49])).
% 0.49/0.77  fof(f136,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) )),
% 0.49/0.77    inference(resolution,[],[f113,f92])).
% 0.49/0.77  fof(f92,plain,(
% 0.49/0.77    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 0.49/0.77    inference(equality_resolution,[],[f63])).
% 0.49/0.77  fof(f63,plain,(
% 0.49/0.77    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 0.49/0.77    inference(cnf_transformation,[],[f25])).
% 0.49/0.77  fof(f25,plain,(
% 0.49/0.77    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(flattening,[],[f24])).
% 0.49/0.77  fof(f24,plain,(
% 0.49/0.77    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(ennf_transformation,[],[f12])).
% 0.49/0.77  fof(f12,axiom,(
% 0.49/0.77    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.49/0.77  fof(f113,plain,(
% 0.49/0.77    ( ! [X17] : (m1_subset_1(k1_yellow_0(sK0,X17),u1_struct_0(sK0))) )),
% 0.49/0.77    inference(resolution,[],[f49,f77])).
% 0.49/0.77  fof(f77,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.49/0.77    inference(cnf_transformation,[],[f31])).
% 0.49/0.77  fof(f31,plain,(
% 0.49/0.77    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(ennf_transformation,[],[f13])).
% 0.49/0.77  fof(f13,axiom,(
% 0.49/0.77    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.49/0.77  fof(f249,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~r1_orders_2(sK0,X1,X0) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) )),
% 0.49/0.77    inference(subsumption_resolution,[],[f244,f43])).
% 0.49/0.77  fof(f244,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X1,X0) | r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.49/0.77    inference(resolution,[],[f114,f42])).
% 0.49/0.77  fof(f42,plain,(
% 0.49/0.77    v13_waybel_0(sK1,sK0)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f114,plain,(
% 0.49/0.77    ( ! [X4,X5,X3] : (~v13_waybel_0(X3,sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X4,X3) | ~r1_orders_2(sK0,X4,X5) | r2_hidden(X5,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.49/0.77    inference(subsumption_resolution,[],[f107,f90])).
% 0.49/0.77  fof(f107,plain,(
% 0.49/0.77    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X4,X3) | ~r1_orders_2(sK0,X4,X5) | r2_hidden(X5,X3) | ~v13_waybel_0(X3,sK0)) )),
% 0.49/0.77    inference(resolution,[],[f49,f58])).
% 0.49/0.77  fof(f58,plain,(
% 0.49/0.77    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f23])).
% 0.49/0.77  fof(f23,plain,(
% 0.49/0.77    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(flattening,[],[f22])).
% 0.49/0.77  fof(f22,plain,(
% 0.49/0.77    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.49/0.77    inference(ennf_transformation,[],[f15])).
% 0.49/0.77  fof(f15,axiom,(
% 0.49/0.77    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.49/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.49/0.77  fof(f43,plain,(
% 0.49/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  fof(f586,plain,(
% 0.49/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.49/0.77    inference(resolution,[],[f585,f93])).
% 0.49/0.77  fof(f93,plain,(
% 0.49/0.77    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.49/0.77    inference(equality_resolution,[],[f79])).
% 0.49/0.77  fof(f79,plain,(
% 0.49/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.49/0.77    inference(cnf_transformation,[],[f32])).
% 0.49/0.77  fof(f585,plain,(
% 0.49/0.77    v1_subset_1(sK1,sK1)),
% 0.49/0.77    inference(subsumption_resolution,[],[f419,f579])).
% 0.49/0.77  fof(f579,plain,(
% 0.49/0.77    r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.49/0.77    inference(resolution,[],[f437,f98])).
% 0.49/0.77  fof(f98,plain,(
% 0.49/0.77    ( ! [X2] : (~m1_subset_1(X2,sK1) | r2_hidden(X2,sK1)) )),
% 0.49/0.77    inference(resolution,[],[f40,f76])).
% 0.49/0.77  fof(f437,plain,(
% 0.49/0.77    m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.49/0.77    inference(backward_demodulation,[],[f138,f418])).
% 0.49/0.77  fof(f138,plain,(
% 0.49/0.77    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.49/0.77    inference(superposition,[],[f113,f103])).
% 0.49/0.77  fof(f419,plain,(
% 0.49/0.77    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.49/0.77    inference(backward_demodulation,[],[f38,f418])).
% 0.49/0.77  fof(f38,plain,(
% 0.49/0.77    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.49/0.77    inference(cnf_transformation,[],[f20])).
% 0.49/0.77  % SZS output end Proof for theBenchmark
% 0.49/0.77  % (19546)------------------------------
% 0.49/0.77  % (19546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.49/0.77  % (19546)Termination reason: Refutation
% 0.49/0.77  
% 0.49/0.77  % (19546)Memory used [KB]: 1918
% 0.49/0.77  % (19546)Time elapsed: 0.181 s
% 0.49/0.77  % (19546)------------------------------
% 0.49/0.77  % (19546)------------------------------
% 0.49/0.78  % (19390)Success in time 0.415 s
%------------------------------------------------------------------------------

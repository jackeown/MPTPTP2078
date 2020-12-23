%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 952 expanded)
%              Number of leaves         :   21 ( 236 expanded)
%              Depth                    :   48
%              Number of atoms          :  605 (2808 expanded)
%              Number of equality atoms :   40 ( 339 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(subsumption_resolution,[],[f428,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f428,plain,(
    v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f427,f58])).

fof(f58,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f427,plain,(
    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f426,f99])).

fof(f99,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f426,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f425,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f425,plain,(
    v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f424,f53])).

fof(f53,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f424,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f423,f103])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f63,f58])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f423,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f420,f386])).

fof(f386,plain,(
    m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f385,f51])).

fof(f385,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f384,f58])).

fof(f384,plain,
    ( m1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f383,f99])).

fof(f383,plain,
    ( m1_subset_1(k1_xboole_0,sK0)
    | ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f344,f83])).

fof(f344,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | m1_subset_1(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f211,f342])).

fof(f342,plain,(
    k1_xboole_0 = sK1(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f341,f51])).

fof(f341,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = sK1(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f340,f58])).

fof(f340,plain,
    ( k1_xboole_0 = sK1(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f339,f99])).

fof(f339,plain,
    ( k1_xboole_0 = sK1(k2_yellow_1(sK0))
    | ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f338,f83])).

fof(f338,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | k1_xboole_0 = sK1(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f337,f211])).

fof(f337,plain,
    ( ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = sK1(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f332,f52])).

fof(f52,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f332,plain,
    ( ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = sK1(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = sK1(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f327,f215])).

fof(f215,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0)
      | ~ r2_hidden(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f214,f211])).

fof(f214,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0) ) ),
    inference(subsumption_resolution,[],[f213,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f213,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0)
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f209,f153])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X1),X3,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X0,X2)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(forward_demodulation,[],[f152,f58])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X0,X2)
      | ~ r1_lattice3(k2_yellow_1(X1),X3,X0) ) ),
    inference(forward_demodulation,[],[f151,f58])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X0,X2)
      | ~ r1_lattice3(k2_yellow_1(X1),X3,X0) ) ),
    inference(resolution,[],[f73,f57])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f209,plain,
    ( r1_lattice3(k2_yellow_1(sK0),sK0,sK1(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f208,f58])).

fof(f208,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f206,f57])).

fof(f206,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f201,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | r1_lattice3(X0,u1_struct_0(X0),sK1(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f201,plain,
    ( v1_yellow_0(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f200,f52])).

fof(f200,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | v1_yellow_0(k2_yellow_1(sK0))
    | ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(resolution,[],[f198,f87])).

fof(f198,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | v1_yellow_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f197,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X1),X1,X0)
      | ~ m1_subset_1(X0,X1)
      | v1_yellow_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f115,f58])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r1_lattice3(k2_yellow_1(X1),u1_struct_0(k2_yellow_1(X1)),X0)
      | v1_yellow_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f114,f58])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ r1_lattice3(k2_yellow_1(X1),u1_struct_0(k2_yellow_1(X1)),X0)
      | v1_yellow_0(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f67,f57])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,(
    ! [X0] :
      ( r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f196,f52])).

fof(f196,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,sK0) ) ),
    inference(resolution,[],[f190,f87])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f189,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f138,f57])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(superposition,[],[f74,f58])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0)
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f188,f58])).

fof(f188,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f185,f57])).

fof(f185,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ) ),
    inference(resolution,[],[f184,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f184,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,X0)
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f183,f52])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) ) ),
    inference(subsumption_resolution,[],[f182,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f182,plain,(
    ! [X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f169,f87])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f168,f107])).

fof(f107,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f89,f100])).

fof(f100,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | v2_struct_0(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X0,X2)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v2_struct_0(k2_yellow_1(X1))
      | r1_orders_2(k2_yellow_1(X1),X0,X2)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(resolution,[],[f166,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f97,f58])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f60,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f165,f58])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f164,f58])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f327,plain,(
    ! [X0] :
      ( ~ r1_orders_2(k2_yellow_1(sK0),X0,k1_xboole_0)
      | ~ m1_subset_1(X0,sK0)
      | k1_xboole_0 = X0
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f326,f52])).

fof(f326,plain,(
    ! [X0] :
      ( ~ r1_orders_2(k2_yellow_1(sK0),X0,k1_xboole_0)
      | ~ m1_subset_1(X0,sK0)
      | k1_xboole_0 = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(k1_xboole_0,sK0) ) ),
    inference(resolution,[],[f323,f87])).

fof(f323,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,sK0)
      | ~ r1_orders_2(k2_yellow_1(sK0),X2,k1_xboole_0)
      | ~ m1_subset_1(X2,sK0)
      | k1_xboole_0 = X2
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r1_orders_2(k2_yellow_1(sK0),X2,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,sK0)
      | k1_xboole_0 = X2
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(resolution,[],[f205,f184])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f204,f58])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f203,f58])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f202,f57])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | X1 = X2 ) ),
    inference(resolution,[],[f82,f56])).

fof(f56,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f211,plain,
    ( m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f210,f58])).

fof(f210,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f207,f57])).

fof(f207,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f201,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f420,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f414,f327])).

fof(f414,plain,(
    ! [X1] :
      ( r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X1)
      | ~ m1_subset_1(X1,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X1)
      | v2_struct_0(k2_yellow_1(sK0))
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f411,f201])).

fof(f411,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | r1_orders_2(k2_yellow_1(X1),k3_yellow_0(k2_yellow_1(X1)),X0)
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(forward_demodulation,[],[f410,f104])).

fof(f104,plain,(
    ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f64,f57])).

% (13126)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f410,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0)
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f409,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f123,f100])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k2_yellow_1(X1),X2,X0),X2)
      | ~ m1_subset_1(X0,X1)
      | r2_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(forward_demodulation,[],[f122,f58])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | r2_hidden(sK4(k2_yellow_1(X1),X2,X0),X2)
      | r2_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(resolution,[],[f79,f57])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f409,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)
      | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0)
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f408,f57])).

fof(f408,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)
      | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0)
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(subsumption_resolution,[],[f407,f56])).

fof(f407,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)
      | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0)
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ v1_yellow_0(k2_yellow_1(X1))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | v2_struct_0(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f406,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f406,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(X2,X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2) ) ),
    inference(forward_demodulation,[],[f405,f58])).

fof(f405,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2) ) ),
    inference(subsumption_resolution,[],[f404,f106])).

fof(f106,plain,(
    ! [X0,X1] : m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f105,f57])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f86,f58])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f404,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0)
      | ~ r1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2) ) ),
    inference(forward_demodulation,[],[f403,f58])).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2) ) ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (13118)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (13110)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (13125)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (13104)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (13109)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (13104)Refutation not found, incomplete strategy% (13104)------------------------------
% 0.20/0.55  % (13104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13104)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13104)Memory used [KB]: 1663
% 0.20/0.55  % (13104)Time elapsed: 0.131 s
% 0.20/0.55  % (13104)------------------------------
% 0.20/0.55  % (13104)------------------------------
% 0.20/0.55  % (13110)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f429,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f428,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ~v1_xboole_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.55    inference(negated_conjecture,[],[f21])).
% 0.20/0.55  fof(f21,conjecture,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.55  fof(f428,plain,(
% 0.20/0.55    v1_xboole_0(sK0)),
% 0.20/0.55    inference(forward_demodulation,[],[f427,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.55  fof(f427,plain,(
% 0.20/0.55    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f426,f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.55    inference(resolution,[],[f62,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.55  fof(f426,plain,(
% 0.20/0.55    ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(resolution,[],[f425,f83])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.20/0.55  fof(f425,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f424,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f424,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f423,f103])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f102,f57])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.55    inference(superposition,[],[f63,f58])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.55  fof(f423,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f420,f386])).
% 0.20/0.55  fof(f386,plain,(
% 0.20/0.55    m1_subset_1(k1_xboole_0,sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f385,f51])).
% 0.20/0.55  fof(f385,plain,(
% 0.20/0.55    v1_xboole_0(sK0) | m1_subset_1(k1_xboole_0,sK0)),
% 0.20/0.55    inference(forward_demodulation,[],[f384,f58])).
% 0.20/0.55  fof(f384,plain,(
% 0.20/0.55    m1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f383,f99])).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    m1_subset_1(k1_xboole_0,sK0) | ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(resolution,[],[f344,f83])).
% 0.20/0.55  fof(f344,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | m1_subset_1(k1_xboole_0,sK0)),
% 0.20/0.55    inference(backward_demodulation,[],[f211,f342])).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    k1_xboole_0 = sK1(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f341,f51])).
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    v1_xboole_0(sK0) | k1_xboole_0 = sK1(k2_yellow_1(sK0))),
% 0.20/0.55    inference(forward_demodulation,[],[f340,f58])).
% 0.20/0.55  fof(f340,plain,(
% 0.20/0.55    k1_xboole_0 = sK1(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f339,f99])).
% 0.20/0.55  fof(f339,plain,(
% 0.20/0.55    k1_xboole_0 = sK1(k2_yellow_1(sK0)) | ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(resolution,[],[f338,f83])).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | k1_xboole_0 = sK1(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f337,f211])).
% 0.20/0.55  fof(f337,plain,(
% 0.20/0.55    ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = sK1(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f332,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f332,plain,(
% 0.20/0.55    ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = sK1(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f331])).
% 0.20/0.55  fof(f331,plain,(
% 0.20/0.55    ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = sK1(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f327,f215])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0) | ~r2_hidden(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f214,f211])).
% 0.20/0.55  fof(f214,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f213,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.55  fof(f213,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1(k2_yellow_1(sK0)),X0) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f209,f153])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r1_lattice3(k2_yellow_1(X1),X3,X0) | ~m1_subset_1(X0,X1) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~m1_subset_1(X2,X1)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f152,f58])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r1_lattice3(k2_yellow_1(X1),X3,X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f151,f58])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~r1_lattice3(k2_yellow_1(X1),X3,X0)) )),
% 0.20/0.55    inference(resolution,[],[f73,f57])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    r1_lattice3(k2_yellow_1(sK0),sK0,sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(forward_demodulation,[],[f208,f58])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | r1_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f206,f57])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | r1_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f201,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_yellow_0(X0) | r1_lattice3(X0,u1_struct_0(X0),sK1(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    v1_yellow_0(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f200,f52])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    v2_struct_0(k2_yellow_1(sK0)) | v1_yellow_0(k2_yellow_1(sK0)) | ~r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.55    inference(resolution,[],[f198,f87])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    ~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | v1_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f197,f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X1),X1,X0) | ~m1_subset_1(X0,X1) | v1_yellow_0(k2_yellow_1(X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f115,f58])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~r1_lattice3(k2_yellow_1(X1),u1_struct_0(k2_yellow_1(X1)),X0) | v1_yellow_0(k2_yellow_1(X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f114,f58])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~r1_lattice3(k2_yellow_1(X1),u1_struct_0(k2_yellow_1(X1)),X0) | v1_yellow_0(k2_yellow_1(X1))) )),
% 0.20/0.55    inference(resolution,[],[f67,f57])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattice3(X0,u1_struct_0(X0),X1) | v1_yellow_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    ( ! [X0] : (r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f196,f52])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f190,f87])).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f189,f139])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f138,f57])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.55    inference(superposition,[],[f74,f58])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f188,f58])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f185,f57])).
% 0.20/0.55  fof(f185,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 0.20/0.55    inference(resolution,[],[f184,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK0),k1_xboole_0,X0) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0)) )),
% 0.20/0.55    inference(resolution,[],[f183,f52])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(k1_xboole_0,X0) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f182,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.56  fof(f182,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | v2_struct_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(resolution,[],[f169,f87])).
% 0.20/0.56  fof(f169,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,X0) | r1_orders_2(k2_yellow_1(X0),k1_xboole_0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(resolution,[],[f168,f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.56    inference(resolution,[],[f89,f100])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(resolution,[],[f85,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f168,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | v2_struct_0(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f167])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | v2_struct_0(k2_yellow_1(X1)) | r1_orders_2(k2_yellow_1(X1),X0,X2) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | ~r1_tarski(X0,X2) | ~m1_subset_1(X2,X1)) )),
% 0.20/0.56    inference(resolution,[],[f166,f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f97,f58])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f60,f58])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,axiom,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f165,f58])).
% 0.20/0.56  fof(f165,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f164,f58])).
% 0.20/0.56  fof(f164,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f163,f57])).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.56    inference(resolution,[],[f92,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.56    inference(pure_predicate_removal,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.56    inference(pure_predicate_removal,[],[f18])).
% 0.20/0.56  fof(f18,axiom,(
% 0.20/0.56    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.56  fof(f327,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_orders_2(k2_yellow_1(sK0),X0,k1_xboole_0) | ~m1_subset_1(X0,sK0) | k1_xboole_0 = X0 | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f326,f52])).
% 0.20/0.56  fof(f326,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_orders_2(k2_yellow_1(sK0),X0,k1_xboole_0) | ~m1_subset_1(X0,sK0) | k1_xboole_0 = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(k1_xboole_0,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f323,f87])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(k1_xboole_0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k1_xboole_0) | ~m1_subset_1(X2,sK0) | k1_xboole_0 = X2 | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f319])).
% 0.20/0.56  fof(f319,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = X2 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X2,sK0)) )),
% 0.20/0.56    inference(resolution,[],[f205,f184])).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | X1 = X2) )),
% 0.20/0.56    inference(forward_demodulation,[],[f204,f58])).
% 0.20/0.56  fof(f204,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | X1 = X2) )),
% 0.20/0.56    inference(forward_demodulation,[],[f203,f58])).
% 0.20/0.56  fof(f203,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | X1 = X2) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f202,f57])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | X1 = X2) )),
% 0.20/0.56    inference(resolution,[],[f82,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.56    inference(flattening,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
% 0.20/0.56  fof(f211,plain,(
% 0.20/0.56    m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.56    inference(forward_demodulation,[],[f210,f58])).
% 0.20/0.56  fof(f210,plain,(
% 0.20/0.56    v2_struct_0(k2_yellow_1(sK0)) | m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.56    inference(subsumption_resolution,[],[f207,f57])).
% 0.20/0.56  fof(f207,plain,(
% 0.20/0.56    v2_struct_0(k2_yellow_1(sK0)) | m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.20/0.56    inference(resolution,[],[f201,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_yellow_0(X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f420,plain,(
% 0.20/0.56    ~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f416])).
% 0.20/0.56  fof(f416,plain,(
% 0.20/0.56    ~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.20/0.56    inference(resolution,[],[f414,f327])).
% 0.20/0.56  fof(f414,plain,(
% 0.20/0.56    ( ! [X1] : (r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X1) | ~m1_subset_1(X1,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f413])).
% 0.20/0.56  fof(f413,plain,(
% 0.20/0.56    ( ! [X1] : (~m1_subset_1(X1,sK0) | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X1) | v2_struct_0(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) )),
% 0.20/0.56    inference(resolution,[],[f411,f201])).
% 0.20/0.56  fof(f411,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_yellow_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | r1_orders_2(k2_yellow_1(X1),k3_yellow_0(k2_yellow_1(X1)),X0) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f410,f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) )),
% 0.20/0.56    inference(resolution,[],[f64,f57])).
% 0.20/0.56  % (13126)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.56  fof(f410,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0) | ~v1_yellow_0(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f409,f135])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.56    inference(resolution,[],[f123,f100])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(k2_yellow_1(X1),X2,X0),X2) | ~m1_subset_1(X0,X1) | r2_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f122,f58])).
% 0.20/0.56  fof(f122,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | r2_hidden(sK4(k2_yellow_1(X1),X2,X0),X2) | r2_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.20/0.56    inference(resolution,[],[f79,f57])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(flattening,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.56  fof(f409,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0) | ~v1_yellow_0(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f408,f57])).
% 0.20/0.56  fof(f408,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0) | ~v1_yellow_0(k2_yellow_1(X1)) | ~l1_orders_2(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f407,f56])).
% 0.20/0.56  fof(f407,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | ~r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) | r1_orders_2(k2_yellow_1(X1),k1_yellow_0(k2_yellow_1(X1),k1_xboole_0),X0) | ~v5_orders_2(k2_yellow_1(X1)) | ~v1_yellow_0(k2_yellow_1(X1)) | ~l1_orders_2(k2_yellow_1(X1)) | v2_struct_0(k2_yellow_1(X1))) )),
% 0.20/0.56    inference(resolution,[],[f406,f81])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.56    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.56  fof(f406,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f405,f58])).
% 0.20/0.56  fof(f405,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f404,f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f105,f57])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.56    inference(superposition,[],[f86,f58])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.56  fof(f404,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0) | ~r1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f403,f58])).
% 0.20/0.56  fof(f403,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),u1_struct_0(k2_yellow_1(X0))) | ~r1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),k1_yellow_0(k2_yellow_1(X0),X1),X2)) )),
% 0.20/0.56    inference(resolution,[],[f94,f57])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 0.20/0.56    inference(equality_resolution,[],[f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(flattening,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (13110)------------------------------
% 0.20/0.56  % (13110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13110)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (13110)Memory used [KB]: 6396
% 0.20/0.56  % (13110)Time elapsed: 0.061 s
% 0.20/0.56  % (13110)------------------------------
% 0.20/0.56  % (13110)------------------------------
% 0.20/0.56  % (13126)Refutation not found, incomplete strategy% (13126)------------------------------
% 0.20/0.56  % (13126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (13126)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (13126)Memory used [KB]: 10746
% 0.20/0.56  % (13126)Time elapsed: 0.130 s
% 0.20/0.56  % (13126)------------------------------
% 0.20/0.56  % (13126)------------------------------
% 0.20/0.56  % (13117)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.56  % (13103)Success in time 0.2 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:50 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   92 (1757 expanded)
%              Number of leaves         :   15 ( 360 expanded)
%              Depth                    :   17
%              Number of atoms          :  417 (10485 expanded)
%              Number of equality atoms :   48 (1032 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2462,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f126,f118,f1306,f55,f168,f1314,f1532,f1033])).

fof(f1033,plain,(
    ! [X4,X3] :
      ( k2_lattices(X3,X4,sK3(X3,X4)) != X4
      | ~ l1_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | v2_struct_0(X3)
      | v13_lattices(X3)
      | ~ m1_subset_1(sK3(X3,X4),u1_struct_0(X3))
      | ~ v6_lattices(X3) ) ),
    inference(duplicate_literal_removal,[],[f1026])).

fof(f1026,plain,(
    ! [X4,X3] :
      ( k2_lattices(X3,X4,sK3(X3,X4)) != X4
      | ~ l1_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | k2_lattices(X3,X4,sK3(X3,X4)) != X4
      | v2_struct_0(X3)
      | v13_lattices(X3)
      | ~ l1_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK3(X3,X4),u1_struct_0(X3))
      | v2_struct_0(X3)
      | ~ v6_lattices(X3) ) ),
    inference(superposition,[],[f78,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK3(X0,X1),X1) != X1
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f1532,plain,(
    ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f130,f55,f132,f58,f168,f1314,f1390,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f1390,plain,(
    ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f56,f57,f58,f55,f168,f1312,f1314,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f1312,plain,(
    ! [X0] : r4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f55,f58,f118,f168,f1306,f304])).

fof(f304,plain,(
    ! [X6,X5] :
      ( r4_lattice3(X5,sK3(X5,X6),k1_xboole_0)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ l1_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | v13_lattices(X5) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X6,X5] :
      ( ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,sK3(X5,X6),k1_xboole_0)
      | ~ l1_lattices(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | v2_struct_0(X5)
      | v13_lattices(X5) ) ),
    inference(resolution,[],[f288,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f288,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | v2_struct_0(X4)
      | r4_lattice3(X4,X5,k1_xboole_0) ) ),
    inference(resolution,[],[f98,f141])).

fof(f141,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f134,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f135,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f135,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(unit_resulting_resolution,[],[f134,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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

fof(f134,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f59,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f57,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f56,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f58,f55,f56,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f130,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f58,f55,f56,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1314,plain,(
    ! [X0] : m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f118,f55,f168,f1306,f79])).

fof(f168,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f58,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1306,plain,(
    ~ v13_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f168,f1295])).

fof(f1295,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0) ),
    inference(global_subsumption,[],[f55,f117,f118,f155,f1285])).

fof(f1285,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f1215,f112])).

fof(f112,plain,(
    ! [X2,X0] :
      ( k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f1215,plain,(
    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f130,f55,f58,f132,f155,f168,f1162,f70])).

fof(f1162,plain,(
    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f56,f58,f57,f55,f285,f155,f168,f115])).

fof(f285,plain,(
    r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f58,f55,f155,f141,f98])).

fof(f155,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f118,f71])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f117,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(global_subsumption,[],[f58,f56,f55,f54])).

fof(f54,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f126,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f58,f55,f56,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (9472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (9480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (9469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (9479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (9478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (9477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (9490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (9471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (9470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (9492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (9481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (9467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (9494)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (9493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (9488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (9466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (9476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (9482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (9491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (9487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (9482)Refutation not found, incomplete strategy% (9482)------------------------------
% 0.22/0.56  % (9482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9482)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9482)Memory used [KB]: 10618
% 0.22/0.56  % (9482)Time elapsed: 0.108 s
% 0.22/0.56  % (9482)------------------------------
% 0.22/0.56  % (9482)------------------------------
% 1.57/0.57  % (9484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.57  % (9483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.57  % (9486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.57  % (9468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.57/0.57  % (9473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.57  % (9475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.57  % (9475)Refutation not found, incomplete strategy% (9475)------------------------------
% 1.57/0.57  % (9475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (9475)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.58  % (9475)Memory used [KB]: 10746
% 1.57/0.58  % (9475)Time elapsed: 0.148 s
% 1.57/0.58  % (9475)------------------------------
% 1.57/0.58  % (9475)------------------------------
% 1.57/0.58  % (9489)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.58  % (9465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.58  % (9465)Refutation not found, incomplete strategy% (9465)------------------------------
% 1.57/0.58  % (9465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (9465)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (9465)Memory used [KB]: 1663
% 1.57/0.58  % (9465)Time elapsed: 0.002 s
% 1.57/0.58  % (9465)------------------------------
% 1.57/0.58  % (9465)------------------------------
% 1.70/0.58  % (9476)Refutation not found, incomplete strategy% (9476)------------------------------
% 1.70/0.58  % (9476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.58  % (9476)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.58  
% 1.70/0.58  % (9476)Memory used [KB]: 10746
% 1.70/0.58  % (9476)Time elapsed: 0.145 s
% 1.70/0.58  % (9476)------------------------------
% 1.70/0.58  % (9476)------------------------------
% 1.70/0.59  % (9487)Refutation not found, incomplete strategy% (9487)------------------------------
% 1.70/0.59  % (9487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (9487)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (9487)Memory used [KB]: 10746
% 1.70/0.59  % (9487)Time elapsed: 0.133 s
% 1.70/0.59  % (9487)------------------------------
% 1.70/0.59  % (9487)------------------------------
% 1.70/0.59  % (9474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.70/0.60  % (9474)Refutation not found, incomplete strategy% (9474)------------------------------
% 1.70/0.60  % (9474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (9474)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (9474)Memory used [KB]: 10618
% 1.70/0.60  % (9474)Time elapsed: 0.007 s
% 1.70/0.60  % (9474)------------------------------
% 1.70/0.60  % (9474)------------------------------
% 2.10/0.69  % (9511)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.56/0.71  % (9505)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.56/0.72  % (9514)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.56/0.73  % (9519)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.56/0.73  % (9517)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.56/0.75  % (9526)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.91/0.83  % (9489)Refutation found. Thanks to Tanya!
% 2.91/0.83  % SZS status Theorem for theBenchmark
% 2.91/0.84  % SZS output start Proof for theBenchmark
% 2.91/0.84  fof(f2462,plain,(
% 2.91/0.84    $false),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f126,f118,f1306,f55,f168,f1314,f1532,f1033])).
% 2.91/0.84  fof(f1033,plain,(
% 2.91/0.84    ( ! [X4,X3] : (k2_lattices(X3,X4,sK3(X3,X4)) != X4 | ~l1_lattices(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | v2_struct_0(X3) | v13_lattices(X3) | ~m1_subset_1(sK3(X3,X4),u1_struct_0(X3)) | ~v6_lattices(X3)) )),
% 2.91/0.84    inference(duplicate_literal_removal,[],[f1026])).
% 2.91/0.84  fof(f1026,plain,(
% 2.91/0.84    ( ! [X4,X3] : (k2_lattices(X3,X4,sK3(X3,X4)) != X4 | ~l1_lattices(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | k2_lattices(X3,X4,sK3(X3,X4)) != X4 | v2_struct_0(X3) | v13_lattices(X3) | ~l1_lattices(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(sK3(X3,X4),u1_struct_0(X3)) | v2_struct_0(X3) | ~v6_lattices(X3)) )),
% 2.91/0.84    inference(superposition,[],[f78,f83])).
% 2.91/0.84  fof(f83,plain,(
% 2.91/0.84    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~v6_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f37])).
% 2.91/0.84  fof(f37,plain,(
% 2.91/0.84    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f36])).
% 2.91/0.84  fof(f36,plain,(
% 2.91/0.84    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f13])).
% 2.91/0.84  fof(f13,axiom,(
% 2.91/0.84    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 2.91/0.84  fof(f78,plain,(
% 2.91/0.84    ( ! [X0,X1] : (k2_lattices(X0,sK3(X0,X1),X1) != X1 | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | v2_struct_0(X0) | v13_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f35])).
% 2.91/0.84  fof(f35,plain,(
% 2.91/0.84    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f34])).
% 2.91/0.84  fof(f34,plain,(
% 2.91/0.84    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f10])).
% 2.91/0.84  fof(f10,axiom,(
% 2.91/0.84    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 2.91/0.84  fof(f1532,plain,(
% 2.91/0.84    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f130,f55,f132,f58,f168,f1314,f1390,f70])).
% 2.91/0.84  fof(f70,plain,(
% 2.91/0.84    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f29])).
% 2.91/0.84  fof(f29,plain,(
% 2.91/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f28])).
% 2.91/0.84  fof(f28,plain,(
% 2.91/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f9])).
% 2.91/0.84  fof(f9,axiom,(
% 2.91/0.84    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 2.91/0.84  fof(f1390,plain,(
% 2.91/0.84    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f56,f57,f58,f55,f168,f1312,f1314,f115])).
% 2.91/0.84  fof(f115,plain,(
% 2.91/0.84    ( ! [X0,X3,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 2.91/0.84    inference(equality_resolution,[],[f94])).
% 2.91/0.84  fof(f94,plain,(
% 2.91/0.84    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 2.91/0.84    inference(cnf_transformation,[],[f45])).
% 2.91/0.84  fof(f45,plain,(
% 2.91/0.84    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f44])).
% 2.91/0.84  fof(f44,plain,(
% 2.91/0.84    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f12])).
% 2.91/0.84  fof(f12,axiom,(
% 2.91/0.84    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 2.91/0.84  fof(f1312,plain,(
% 2.91/0.84    ( ! [X0] : (r4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)),k1_xboole_0)) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f55,f58,f118,f168,f1306,f304])).
% 2.91/0.84  fof(f304,plain,(
% 2.91/0.84    ( ! [X6,X5] : (r4_lattice3(X5,sK3(X5,X6),k1_xboole_0) | v2_struct_0(X5) | ~l3_lattices(X5) | ~l1_lattices(X5) | ~m1_subset_1(X6,u1_struct_0(X5)) | v13_lattices(X5)) )),
% 2.91/0.84    inference(duplicate_literal_removal,[],[f299])).
% 2.91/0.84  fof(f299,plain,(
% 2.91/0.84    ( ! [X6,X5] : (~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,sK3(X5,X6),k1_xboole_0) | ~l1_lattices(X5) | ~m1_subset_1(X6,u1_struct_0(X5)) | v2_struct_0(X5) | v13_lattices(X5)) )),
% 2.91/0.84    inference(resolution,[],[f288,f79])).
% 2.91/0.84  fof(f79,plain,(
% 2.91/0.84    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f35])).
% 2.91/0.84  fof(f288,plain,(
% 2.91/0.84    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | v2_struct_0(X4) | r4_lattice3(X4,X5,k1_xboole_0)) )),
% 2.91/0.84    inference(resolution,[],[f98,f141])).
% 2.91/0.84  fof(f141,plain,(
% 2.91/0.84    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.91/0.84    inference(backward_demodulation,[],[f134,f138])).
% 2.91/0.84  fof(f138,plain,(
% 2.91/0.84    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f135,f68])).
% 2.91/0.84  fof(f68,plain,(
% 2.91/0.84    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.91/0.84    inference(cnf_transformation,[],[f27])).
% 2.91/0.84  fof(f27,plain,(
% 2.91/0.84    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.91/0.84    inference(ennf_transformation,[],[f3])).
% 2.91/0.84  fof(f3,axiom,(
% 2.91/0.84    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.91/0.84  fof(f135,plain,(
% 2.91/0.84    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f134,f104])).
% 2.91/0.84  fof(f104,plain,(
% 2.91/0.84    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f51])).
% 2.91/0.84  fof(f51,plain,(
% 2.91/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f1])).
% 2.91/0.84  fof(f1,axiom,(
% 2.91/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.91/0.84  fof(f134,plain,(
% 2.91/0.84    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f59,f100])).
% 2.91/0.84  fof(f100,plain,(
% 2.91/0.84    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f48])).
% 2.91/0.84  fof(f48,plain,(
% 2.91/0.84    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.91/0.84    inference(ennf_transformation,[],[f21])).
% 2.91/0.84  fof(f21,plain,(
% 2.91/0.84    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.91/0.84    inference(rectify,[],[f2])).
% 2.91/0.84  fof(f2,axiom,(
% 2.91/0.84    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.91/0.84  fof(f59,plain,(
% 2.91/0.84    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f4])).
% 2.91/0.84  fof(f4,axiom,(
% 2.91/0.84    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.91/0.84  fof(f98,plain,(
% 2.91/0.84    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r4_lattice3(X0,X1,X2)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f47])).
% 2.91/0.84  fof(f47,plain,(
% 2.91/0.84    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f46])).
% 2.91/0.84  fof(f46,plain,(
% 2.91/0.84    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f11])).
% 2.91/0.84  fof(f11,axiom,(
% 2.91/0.84    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.91/0.84  fof(f57,plain,(
% 2.91/0.84    v4_lattice3(sK0)),
% 2.91/0.84    inference(cnf_transformation,[],[f23])).
% 2.91/0.84  fof(f23,plain,(
% 2.91/0.84    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f22])).
% 2.91/0.84  fof(f22,plain,(
% 2.91/0.84    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f20])).
% 2.91/0.84  fof(f20,negated_conjecture,(
% 2.91/0.84    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.91/0.84    inference(negated_conjecture,[],[f19])).
% 2.91/0.84  fof(f19,conjecture,(
% 2.91/0.84    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 2.91/0.84  fof(f56,plain,(
% 2.91/0.84    v10_lattices(sK0)),
% 2.91/0.84    inference(cnf_transformation,[],[f23])).
% 2.91/0.84  fof(f58,plain,(
% 2.91/0.84    l3_lattices(sK0)),
% 2.91/0.84    inference(cnf_transformation,[],[f23])).
% 2.91/0.84  fof(f132,plain,(
% 2.91/0.84    v9_lattices(sK0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f58,f55,f56,f67])).
% 2.91/0.84  fof(f67,plain,(
% 2.91/0.84    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f26])).
% 2.91/0.84  fof(f26,plain,(
% 2.91/0.84    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.91/0.84    inference(flattening,[],[f25])).
% 2.91/0.84  fof(f25,plain,(
% 2.91/0.84    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.91/0.84    inference(ennf_transformation,[],[f5])).
% 2.91/0.84  fof(f5,axiom,(
% 2.91/0.84    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.91/0.84  fof(f130,plain,(
% 2.91/0.84    v8_lattices(sK0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f58,f55,f56,f66])).
% 2.91/0.84  fof(f66,plain,(
% 2.91/0.84    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f26])).
% 2.91/0.84  fof(f1314,plain,(
% 2.91/0.84    ( ! [X0] : (m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f118,f55,f168,f1306,f79])).
% 2.91/0.84  fof(f168,plain,(
% 2.91/0.84    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f55,f58,f102])).
% 2.91/0.84  fof(f102,plain,(
% 2.91/0.84    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f50])).
% 2.91/0.84  fof(f50,plain,(
% 2.91/0.84    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f49])).
% 2.91/0.84  fof(f49,plain,(
% 2.91/0.84    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f14])).
% 2.91/0.84  fof(f14,axiom,(
% 2.91/0.84    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 2.91/0.84  fof(f55,plain,(
% 2.91/0.84    ~v2_struct_0(sK0)),
% 2.91/0.84    inference(cnf_transformation,[],[f23])).
% 2.91/0.84  fof(f1306,plain,(
% 2.91/0.84    ~v13_lattices(sK0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f168,f1295])).
% 2.91/0.84  fof(f1295,plain,(
% 2.91/0.84    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~v13_lattices(sK0)),
% 2.91/0.84    inference(global_subsumption,[],[f55,f117,f118,f155,f1285])).
% 2.91/0.84  fof(f1285,plain,(
% 2.91/0.84    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~l1_lattices(sK0) | ~v13_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 2.91/0.84    inference(superposition,[],[f1215,f112])).
% 2.91/0.84  fof(f112,plain,(
% 2.91/0.84    ( ! [X2,X0] : (k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.91/0.84    inference(equality_resolution,[],[f74])).
% 2.91/0.84  fof(f74,plain,(
% 2.91/0.84    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 2.91/0.84    inference(cnf_transformation,[],[f33])).
% 2.91/0.84  fof(f33,plain,(
% 2.91/0.84    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f32])).
% 2.91/0.84  fof(f32,plain,(
% 2.91/0.84    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f6])).
% 2.91/0.84  fof(f6,axiom,(
% 2.91/0.84    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 2.91/0.84  fof(f1215,plain,(
% 2.91/0.84    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f130,f55,f58,f132,f155,f168,f1162,f70])).
% 2.91/0.84  fof(f1162,plain,(
% 2.91/0.84    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f56,f58,f57,f55,f285,f155,f168,f115])).
% 2.91/0.84  fof(f285,plain,(
% 2.91/0.84    r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f58,f55,f155,f141,f98])).
% 2.91/0.84  fof(f155,plain,(
% 2.91/0.84    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f55,f118,f71])).
% 2.91/0.84  fof(f71,plain,(
% 2.91/0.84    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f31])).
% 2.91/0.84  fof(f31,plain,(
% 2.91/0.84    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.91/0.84    inference(flattening,[],[f30])).
% 2.91/0.84  fof(f30,plain,(
% 2.91/0.84    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.91/0.84    inference(ennf_transformation,[],[f7])).
% 2.91/0.84  fof(f7,axiom,(
% 2.91/0.84    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 2.91/0.84  fof(f117,plain,(
% 2.91/0.84    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 2.91/0.84    inference(global_subsumption,[],[f58,f56,f55,f54])).
% 2.91/0.84  fof(f54,plain,(
% 2.91/0.84    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 2.91/0.84    inference(cnf_transformation,[],[f23])).
% 2.91/0.84  fof(f118,plain,(
% 2.91/0.84    l1_lattices(sK0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f58,f60])).
% 2.91/0.84  fof(f60,plain,(
% 2.91/0.84    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f24])).
% 2.91/0.84  fof(f24,plain,(
% 2.91/0.84    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.91/0.84    inference(ennf_transformation,[],[f8])).
% 2.91/0.84  fof(f8,axiom,(
% 2.91/0.84    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.91/0.84    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.91/0.84  fof(f126,plain,(
% 2.91/0.84    v6_lattices(sK0)),
% 2.91/0.84    inference(unit_resulting_resolution,[],[f58,f55,f56,f64])).
% 2.91/0.84  fof(f64,plain,(
% 2.91/0.84    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 2.91/0.84    inference(cnf_transformation,[],[f26])).
% 2.91/0.84  % SZS output end Proof for theBenchmark
% 2.91/0.84  % (9489)------------------------------
% 2.91/0.84  % (9489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.84  % (9489)Termination reason: Refutation
% 2.91/0.84  
% 2.91/0.84  % (9489)Memory used [KB]: 8827
% 2.91/0.84  % (9489)Time elapsed: 0.417 s
% 2.91/0.84  % (9489)------------------------------
% 2.91/0.84  % (9489)------------------------------
% 2.91/0.84  % (9464)Success in time 0.474 s
%------------------------------------------------------------------------------

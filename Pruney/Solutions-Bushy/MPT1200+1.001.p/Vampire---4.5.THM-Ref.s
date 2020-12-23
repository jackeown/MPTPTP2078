%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1200+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:28 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 246 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  289 (1643 expanded)
%              Number of equality atoms :   41 (  41 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1635,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1633,f1353])).

fof(f1353,plain,(
    k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f1349,f331])).

fof(f331,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattices(X0,X1,X2)
                     => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(f103,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,X1,sK3),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f102,f83])).

fof(f83,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f31,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,X1,sK3),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k2_lattices(sK0,X1,sK3),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f22,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1349,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(resolution,[],[f276,f330])).

fof(f330,plain,(
    m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f276,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f275,f84])).

fof(f84,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f275,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f271,f27])).

fof(f271,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(resolution,[],[f24,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f24,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1633,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f804,f1615])).

fof(f1615,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) ),
    inference(resolution,[],[f317,f22])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f316,f28])).

fof(f28,plain,(
    v7_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f316,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f315,f25])).

fof(f315,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f314,f26])).

fof(f314,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f313,f83])).

fof(f313,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0))
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f309,f27])).

fof(f309,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,X0))
      | v2_struct_0(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_lattices(sK0) ) ),
    inference(superposition,[],[f37,f154])).

fof(f154,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f153,f25])).

fof(f153,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f152,f26])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f151,f31])).

fof(f151,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f150,f30])).

fof(f30,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f150,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f149,f29])).

fof(f29,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f149,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f144,f27])).

fof(f144,plain,
    ( v2_struct_0(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f23,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f23,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
      | ~ v7_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

fof(f804,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3)) ),
    inference(resolution,[],[f330,f234])).

fof(f234,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X2),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f233,f29])).

fof(f233,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X2),X2) = X2
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f31])).

fof(f232,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X2),X2) = X2
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f27])).

fof(f215,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X2),X2) = X2
      | ~ v8_lattices(sK0) ) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

%------------------------------------------------------------------------------

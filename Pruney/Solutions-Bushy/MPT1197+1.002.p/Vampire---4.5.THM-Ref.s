%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1197+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 224 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :   24
%              Number of atoms          :  259 (1137 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f291,plain,(
    $false ),
    inference(subsumption_resolution,[],[f288,f23])).

fof(f23,plain,(
    ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f288,plain,(
    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f252,f278])).

fof(f278,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f271,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f271,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,sK2) = k4_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f270,f25])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k4_lattices(sK0,X0,sK2) = k4_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f269,f40])).

fof(f40,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f269,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k4_lattices(sK0,X0,sK2) = k4_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f261,f26])).

fof(f26,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f261,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k4_lattices(sK0,X0,sK2) = k4_lattices(sK0,sK2,X0) ) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f252,plain,(
    r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f251,f25])).

fof(f251,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f24])).

fof(f250,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f22])).

fof(f249,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f40])).

fof(f248,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f247,f26])).

fof(f247,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f222,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f222,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1) ),
    inference(forward_demodulation,[],[f220,f215])).

fof(f215,plain,(
    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f194,f22])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,sK1) = k4_lattices(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f193,f25])).

fof(f193,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,sK1) = k4_lattices(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f192,f40])).

fof(f192,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,sK1) = k4_lattices(sK0,X1,sK1) ) ),
    inference(subsumption_resolution,[],[f182,f26])).

fof(f182,plain,(
    ! [X1] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,sK1) = k4_lattices(sK0,X1,sK1) ) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f220,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f87,f215])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f86,f25])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f85,f24])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(subsumption_resolution,[],[f84,f41])).

fof(f41,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f30,f28])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( sK1 != sK1
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(superposition,[],[f31,f75])).

fof(f75,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f55,f22])).

fof(f55,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X1,sK1),sK1) ) ),
    inference(subsumption_resolution,[],[f54,f27])).

fof(f27,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X1,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f53,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X1,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f43,plain,(
    ! [X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | sK1 = k1_lattices(sK0,k2_lattices(sK0,X1,sK1),sK1)
      | ~ v8_lattices(sK0) ) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

%------------------------------------------------------------------------------

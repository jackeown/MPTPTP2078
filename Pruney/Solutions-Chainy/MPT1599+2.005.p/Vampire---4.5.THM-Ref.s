%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 919 expanded)
%              Number of leaves         :   29 ( 312 expanded)
%              Depth                    :   31
%              Number of atoms          : 1035 (4240 expanded)
%              Number of equality atoms :   85 ( 314 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1718,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f156,f218,f663,f743,f755,f1077,f1636,f1717])).

fof(f1717,plain,
    ( spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f1716])).

fof(f1716,plain,
    ( $false
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1715,f52])).

fof(f52,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    & v2_lattice3(k2_yellow_1(sK2))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
      & v2_lattice3(k2_yellow_1(sK2))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
      & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f1715,plain,
    ( v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1714,f631])).

fof(f631,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl6_24
  <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1714,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | spl6_1
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1713,f103])).

fof(f103,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1713,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1711,f96])).

fof(f96,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f54,f63])).

fof(f63,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f54,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f1711,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(resolution,[],[f1694,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f111,f63])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f1694,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1693,f631])).

fof(f1693,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1692,f63])).

fof(f1692,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1691,f96])).

fof(f1691,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1690,f63])).

fof(f1690,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1689,f58])).

fof(f58,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f1689,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1688,f60])).

fof(f60,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f1688,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1687,f53])).

fof(f53,plain,(
    v2_lattice3(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f1687,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1686,f62])).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f1686,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f1685,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1685,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(duplicate_literal_removal,[],[f1682])).

fof(f1682,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(superposition,[],[f223,f1607])).

fof(f1607,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f1602,f1127])).

fof(f1127,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(backward_demodulation,[],[f665,f742])).

fof(f742,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl6_28
  <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f665,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_24 ),
    inference(resolution,[],[f631,f141])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1) ) ),
    inference(subsumption_resolution,[],[f136,f53])).

fof(f136,plain,(
    ! [X1] :
      ( k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1)
      | ~ m1_subset_1(X1,sK2)
      | ~ v2_lattice3(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f134,f96])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f133,f60])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f80,f63])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f1602,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_24 ),
    inference(resolution,[],[f678,f96])).

fof(f678,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2)
        | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) )
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f673,f53])).

fof(f673,plain,
    ( ! [X2] :
        ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2)
        | ~ m1_subset_1(X2,sK2)
        | ~ v2_lattice3(k2_yellow_1(sK2)) )
    | ~ spl6_24 ),
    inference(resolution,[],[f631,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f162,f60])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f160,f62])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f86,f63])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k12_lattice3(X1,X0,X2),X0)
      | ~ r1_tarski(X0,k12_lattice3(X1,X0,X2))
      | r3_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(extensionality_resolution,[],[f85,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) != X1
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1636,plain,
    ( spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f1635])).

fof(f1635,plain,
    ( $false
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1634,f52])).

fof(f1634,plain,
    ( v1_xboole_0(sK2)
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1633,f631])).

fof(f1633,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | spl6_2
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1632,f107])).

fof(f107,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_2
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1632,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1630,f95])).

fof(f95,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f55,f63])).

fof(f55,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f1630,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(resolution,[],[f1621,f112])).

fof(f1621,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1620,f631])).

fof(f1620,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1619,f63])).

fof(f1619,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1618,f95])).

fof(f1618,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1617,f63])).

fof(f1617,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1616,f58])).

fof(f1616,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1615,f60])).

fof(f1615,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1614,f53])).

fof(f1614,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1613,f62])).

fof(f1613,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f1612,f93])).

fof(f1612,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(duplicate_literal_removal,[],[f1609])).

fof(f1609,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(superposition,[],[f223,f1606])).

fof(f1606,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f1601,f1201])).

fof(f1201,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f172,f754])).

fof(f754,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f752])).

fof(f752,plain,
    ( spl6_29
  <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f172,plain,(
    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    inference(resolution,[],[f167,f96])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,sK4)) ) ),
    inference(resolution,[],[f144,f95])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,X1),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,X1))
      | ~ m1_subset_1(X0,sK2) ) ),
    inference(resolution,[],[f140,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f109,f62])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f87,f63])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0) ) ),
    inference(subsumption_resolution,[],[f135,f53])).

fof(f135,plain,(
    ! [X0] :
      ( k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0)
      | ~ m1_subset_1(X0,sK2)
      | ~ v2_lattice3(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f134,f95])).

fof(f1601,plain,
    ( k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_24 ),
    inference(resolution,[],[f678,f95])).

fof(f1077,plain,
    ( ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1075,f96])).

fof(f1075,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(forward_demodulation,[],[f1074,f63])).

fof(f1074,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | ~ spl6_24
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1073,f631])).

fof(f1073,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(forward_demodulation,[],[f1072,f63])).

fof(f1072,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1071,f95])).

fof(f1071,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(forward_demodulation,[],[f1070,f63])).

fof(f1070,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1069,f220])).

fof(f220,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f151,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
          & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r1_orders_2(X1,X4,X0)
            & r1_orders_2(X1,X4,X2)
            & r1_orders_2(X1,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r1_orders_2(X0,X4,X3)
            & r1_orders_2(X0,X4,X2)
            & r1_orders_2(X0,X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r1_orders_2(X0,X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r1_orders_2(X0,X4,X3)
            & r1_orders_2(X0,X4,X2)
            & r1_orders_2(X0,X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r1_orders_2(X0,X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ( ! [X4] :
            ( r1_orders_2(X0,X4,X3)
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r1_orders_2(X0,X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_orders_2(X0,X3,X2)
        & r1_orders_2(X0,X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f151,plain,
    ( sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_3
  <=> sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1069,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1068,f221])).

fof(f221,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ spl6_3 ),
    inference(resolution,[],[f151,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1068,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1067,f60])).

fof(f1067,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1066,f53])).

fof(f1066,plain,
    ( ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1047,f62])).

fof(f1047,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_27 ),
    inference(resolution,[],[f375,f738])).

fof(f738,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl6_27
  <=> r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f375,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,k11_lattice3(X1,X0,X2))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X3,X2)
      | ~ r1_orders_2(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f190,f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X5,X2)
      | ~ r1_orders_2(X1,X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r1_orders_2(X1,X5,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f190,plain,(
    ! [X6,X4,X5] :
      ( sP0(k11_lattice3(X4,X5,X6),X4,X6,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f187,f87])).

fof(f187,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | sP0(k11_lattice3(X4,X5,X6),X4,X6,X5) ) ),
    inference(resolution,[],[f170,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2,k11_lattice3(X2,X0,X1))
      | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k11_lattice3(X2,X0,X1) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k11_lattice3(X2,X0,X1) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k11_lattice3(X2,X0,X1) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X2,X0,X3] :
      ( ( ( k11_lattice3(X0,X1,X2) = X3
          | ~ sP0(X3,X0,X2,X1) )
        & ( sP0(X3,X0,X2,X1)
          | k11_lattice3(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k11_lattice3(X0,X1,X2) = X3
      <=> sP0(X3,X0,X2,X1) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X1,X2,X0,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f755,plain,
    ( ~ spl6_27
    | spl6_29
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f750,f630,f149,f752,f736])).

fof(f750,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f749,f631])).

fof(f749,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f748,f63])).

fof(f748,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f747,f95])).

fof(f747,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f746,f63])).

fof(f746,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f745,f60])).

fof(f745,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f744,f53])).

fof(f744,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f716,f62])).

fof(f716,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f446,f221])).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k11_lattice3(X1,X2,X0) = X0
      | ~ r1_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f438])).

fof(f438,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k11_lattice3(X1,X2,X0) = X0
      | ~ r1_orders_2(X1,X0,X0)
      | ~ r1_orders_2(X1,X0,X2) ) ),
    inference(resolution,[],[f186,f120])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5)
      | sP0(X3,X4,X3,X5)
      | ~ r1_orders_2(X4,X3,X3)
      | ~ r1_orders_2(X4,X3,X5) ) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
      | sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
      | sP0(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k11_lattice3(X1,X3,X2) = X0 ) ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X3,X2,X1,X0)
      | k11_lattice3(X2,X0,X1) = X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f743,plain,
    ( ~ spl6_27
    | spl6_28
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f734,f630,f149,f740,f736])).

fof(f734,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f733,f631])).

fof(f733,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f732,f63])).

fof(f732,plain,
    ( k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f731,f96])).

fof(f731,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f730,f63])).

fof(f730,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f729,f60])).

fof(f729,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f728,f53])).

% (8546)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
fof(f728,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f715,f62])).

fof(f715,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ spl6_3 ),
    inference(resolution,[],[f446,f220])).

fof(f663,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl6_24 ),
    inference(subsumption_resolution,[],[f661,f96])).

fof(f661,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl6_24 ),
    inference(subsumption_resolution,[],[f660,f95])).

fof(f660,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | spl6_24 ),
    inference(resolution,[],[f632,f110])).

fof(f632,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f630])).

fof(f218,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f216,f96])).

fof(f216,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f215,f95])).

fof(f215,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | spl6_4 ),
    inference(resolution,[],[f198,f110])).

fof(f198,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f197,f95])).

fof(f197,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | spl6_4 ),
    inference(forward_demodulation,[],[f196,f63])).

fof(f196,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f195,f96])).

fof(f195,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(forward_demodulation,[],[f194,f63])).

fof(f194,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(forward_demodulation,[],[f193,f63])).

fof(f193,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f192,f60])).

fof(f192,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f191,f53])).

fof(f191,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f188,f62])).

fof(f188,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2))
    | ~ v5_orders_2(k2_yellow_1(sK2))
    | spl6_4 ),
    inference(resolution,[],[f170,f155])).

fof(f155,plain,
    ( ~ sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_4
  <=> sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f156,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f147,f153,f149])).

fof(f147,plain,
    ( ~ sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) ),
    inference(superposition,[],[f92,f143])).

fof(f143,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3) ),
    inference(resolution,[],[f140,f96])).

fof(f108,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f99,f105,f101])).

fof(f99,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) ),
    inference(resolution,[],[f91,f90])).

fof(f90,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) ),
    inference(definition_unfolding,[],[f56,f89])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f81,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:56:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.47  % (8524)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.49  % (8540)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.49  % (8540)Refutation not found, incomplete strategy% (8540)------------------------------
% 0.23/0.49  % (8540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (8540)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (8540)Memory used [KB]: 6268
% 0.23/0.49  % (8540)Time elapsed: 0.065 s
% 0.23/0.49  % (8540)------------------------------
% 0.23/0.49  % (8540)------------------------------
% 0.23/0.52  % (8517)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.52  % (8519)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.52  % (8518)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.52  % (8516)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (8535)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.54  % (8527)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.54  % (8520)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (8516)Refutation not found, incomplete strategy% (8516)------------------------------
% 0.23/0.55  % (8516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8516)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8516)Memory used [KB]: 1663
% 0.23/0.55  % (8516)Time elapsed: 0.126 s
% 0.23/0.55  % (8516)------------------------------
% 0.23/0.55  % (8516)------------------------------
% 0.23/0.55  % (8521)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.55  % (8538)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.55  % (8543)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.55  % (8544)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (8544)Refutation not found, incomplete strategy% (8544)------------------------------
% 0.23/0.55  % (8544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8544)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8544)Memory used [KB]: 1663
% 0.23/0.55  % (8544)Time elapsed: 0.139 s
% 0.23/0.55  % (8544)------------------------------
% 0.23/0.55  % (8544)------------------------------
% 0.23/0.55  % (8532)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.55  % (8543)Refutation not found, incomplete strategy% (8543)------------------------------
% 0.23/0.55  % (8543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8543)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8543)Memory used [KB]: 10746
% 0.23/0.55  % (8543)Time elapsed: 0.141 s
% 0.23/0.55  % (8543)------------------------------
% 0.23/0.55  % (8543)------------------------------
% 0.23/0.55  % (8515)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.55  % (8536)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.55  % (8532)Refutation not found, incomplete strategy% (8532)------------------------------
% 0.23/0.55  % (8532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8532)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8532)Memory used [KB]: 1791
% 0.23/0.55  % (8532)Time elapsed: 0.138 s
% 0.23/0.55  % (8532)------------------------------
% 0.23/0.55  % (8532)------------------------------
% 0.23/0.55  % (8541)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (8542)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (8529)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (8541)Refutation not found, incomplete strategy% (8541)------------------------------
% 0.23/0.55  % (8541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8541)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8541)Memory used [KB]: 6268
% 0.23/0.55  % (8541)Time elapsed: 0.137 s
% 0.23/0.55  % (8541)------------------------------
% 0.23/0.55  % (8541)------------------------------
% 0.23/0.55  % (8529)Refutation not found, incomplete strategy% (8529)------------------------------
% 0.23/0.55  % (8529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8529)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8529)Memory used [KB]: 1791
% 0.23/0.55  % (8529)Time elapsed: 0.109 s
% 0.23/0.55  % (8529)------------------------------
% 0.23/0.55  % (8529)------------------------------
% 0.23/0.55  % (8542)Refutation not found, incomplete strategy% (8542)------------------------------
% 0.23/0.55  % (8542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (8542)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (8542)Memory used [KB]: 6268
% 0.23/0.55  % (8542)Time elapsed: 0.138 s
% 0.23/0.55  % (8542)------------------------------
% 0.23/0.55  % (8542)------------------------------
% 0.23/0.55  % (8537)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.56  % (8531)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (8523)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.56  % (8528)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (8533)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.56  % (8534)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (8525)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.56  % (8526)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.56  % (8539)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.56  % (8522)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (8526)Refutation not found, incomplete strategy% (8526)------------------------------
% 0.23/0.56  % (8526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (8526)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (8526)Memory used [KB]: 6268
% 0.23/0.56  % (8526)Time elapsed: 0.149 s
% 0.23/0.56  % (8526)------------------------------
% 0.23/0.56  % (8526)------------------------------
% 0.23/0.56  % (8530)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.56  % (8525)Refutation not found, incomplete strategy% (8525)------------------------------
% 0.23/0.56  % (8525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (8531)Refutation not found, incomplete strategy% (8531)------------------------------
% 0.23/0.57  % (8531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (8531)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (8531)Memory used [KB]: 10746
% 0.23/0.57  % (8531)Time elapsed: 0.149 s
% 0.23/0.57  % (8531)------------------------------
% 0.23/0.57  % (8531)------------------------------
% 0.23/0.57  % (8525)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (8525)Memory used [KB]: 10746
% 0.23/0.57  % (8525)Time elapsed: 0.153 s
% 0.23/0.57  % (8525)------------------------------
% 0.23/0.57  % (8525)------------------------------
% 1.69/0.60  % (8545)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.11/0.66  % (8521)Refutation found. Thanks to Tanya!
% 2.11/0.66  % SZS status Theorem for theBenchmark
% 2.11/0.66  % SZS output start Proof for theBenchmark
% 2.11/0.66  fof(f1718,plain,(
% 2.11/0.66    $false),
% 2.11/0.66    inference(avatar_sat_refutation,[],[f108,f156,f218,f663,f743,f755,f1077,f1636,f1717])).
% 2.11/0.66  fof(f1717,plain,(
% 2.11/0.66    spl6_1 | ~spl6_24 | ~spl6_28),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f1716])).
% 2.11/0.66  fof(f1716,plain,(
% 2.11/0.66    $false | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1715,f52])).
% 2.11/0.66  fof(f52,plain,(
% 2.11/0.66    ~v1_xboole_0(sK2)),
% 2.11/0.66    inference(cnf_transformation,[],[f40])).
% 2.11/0.66  fof(f40,plain,(
% 2.11/0.66    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2)),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f39,f38,f37])).
% 2.11/0.66  fof(f37,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f38,plain,(
% 2.11/0.66    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f39,plain,(
% 2.11/0.66    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f18,plain,(
% 2.11/0.66    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 2.11/0.66    inference(flattening,[],[f17])).
% 2.11/0.66  fof(f17,plain,(
% 2.11/0.66    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f16])).
% 2.11/0.66  fof(f16,negated_conjecture,(
% 2.11/0.66    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.11/0.66    inference(negated_conjecture,[],[f15])).
% 2.11/0.66  fof(f15,conjecture,(
% 2.11/0.66    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 2.11/0.66  fof(f1715,plain,(
% 2.11/0.66    v1_xboole_0(sK2) | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1714,f631])).
% 2.11/0.66  fof(f631,plain,(
% 2.11/0.66    m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~spl6_24),
% 2.11/0.66    inference(avatar_component_clause,[],[f630])).
% 2.11/0.66  fof(f630,plain,(
% 2.11/0.66    spl6_24 <=> m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.11/0.66  fof(f1714,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (spl6_1 | ~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1713,f103])).
% 2.11/0.66  fof(f103,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | spl6_1),
% 2.11/0.66    inference(avatar_component_clause,[],[f101])).
% 2.11/0.66  fof(f101,plain,(
% 2.11/0.66    spl6_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.11/0.66  fof(f1713,plain,(
% 2.11/0.66    r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1711,f96])).
% 2.11/0.66  fof(f96,plain,(
% 2.11/0.66    m1_subset_1(sK3,sK2)),
% 2.11/0.66    inference(backward_demodulation,[],[f54,f63])).
% 2.11/0.66  fof(f63,plain,(
% 2.11/0.66    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.11/0.66    inference(cnf_transformation,[],[f13])).
% 2.11/0.66  fof(f13,axiom,(
% 2.11/0.66    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 2.11/0.66  fof(f54,plain,(
% 2.11/0.66    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))),
% 2.11/0.66    inference(cnf_transformation,[],[f40])).
% 2.11/0.66  fof(f1711,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,sK2) | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(resolution,[],[f1694,f112])).
% 2.11/0.66  fof(f112,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.11/0.66    inference(forward_demodulation,[],[f111,f63])).
% 2.11/0.66  fof(f111,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.11/0.66    inference(forward_demodulation,[],[f65,f63])).
% 2.11/0.66  fof(f65,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f41])).
% 2.11/0.66  fof(f41,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.11/0.66    inference(nnf_transformation,[],[f19])).
% 2.11/0.66  fof(f19,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f14])).
% 2.11/0.66  fof(f14,axiom,(
% 2.11/0.66    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 2.11/0.66  fof(f1694,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1693,f631])).
% 2.11/0.66  fof(f1693,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(forward_demodulation,[],[f1692,f63])).
% 2.11/0.66  fof(f1692,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1691,f96])).
% 2.11/0.66  fof(f1691,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(forward_demodulation,[],[f1690,f63])).
% 2.11/0.66  fof(f1690,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1689,f58])).
% 2.11/0.66  fof(f58,plain,(
% 2.11/0.66    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f12,axiom,(
% 2.11/0.66    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 2.11/0.66  fof(f1689,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1688,f60])).
% 2.11/0.66  fof(f60,plain,(
% 2.11/0.66    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f12])).
% 2.11/0.66  fof(f1688,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1687,f53])).
% 2.11/0.66  fof(f53,plain,(
% 2.11/0.66    v2_lattice3(k2_yellow_1(sK2))),
% 2.11/0.66    inference(cnf_transformation,[],[f40])).
% 2.11/0.66  fof(f1687,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1686,f62])).
% 2.11/0.66  fof(f62,plain,(
% 2.11/0.66    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f11])).
% 2.11/0.66  fof(f11,axiom,(
% 2.11/0.66    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 2.11/0.66  fof(f1686,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1685,f93])).
% 2.11/0.66  fof(f93,plain,(
% 2.11/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/0.66    inference(equality_resolution,[],[f84])).
% 2.11/0.66  fof(f84,plain,(
% 2.11/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.11/0.66    inference(cnf_transformation,[],[f51])).
% 2.11/0.66  fof(f51,plain,(
% 2.11/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.66    inference(flattening,[],[f50])).
% 2.11/0.66  fof(f50,plain,(
% 2.11/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.66    inference(nnf_transformation,[],[f1])).
% 2.11/0.66  fof(f1,axiom,(
% 2.11/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.66  fof(f1685,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1682])).
% 2.11/0.66  fof(f1682,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(superposition,[],[f223,f1607])).
% 2.11/0.66  fof(f1607,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(forward_demodulation,[],[f1602,f1127])).
% 2.11/0.66  fof(f1127,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | (~spl6_24 | ~spl6_28)),
% 2.11/0.66    inference(backward_demodulation,[],[f665,f742])).
% 2.11/0.66  fof(f742,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_28),
% 2.11/0.66    inference(avatar_component_clause,[],[f740])).
% 2.11/0.66  fof(f740,plain,(
% 2.11/0.66    spl6_28 <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.11/0.66  fof(f665,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_24),
% 2.11/0.66    inference(resolution,[],[f631,f141])).
% 2.11/0.66  fof(f141,plain,(
% 2.11/0.66    ( ! [X1] : (~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f136,f53])).
% 2.11/0.66  fof(f136,plain,(
% 2.11/0.66    ( ! [X1] : (k11_lattice3(k2_yellow_1(sK2),X1,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X1) | ~m1_subset_1(X1,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) )),
% 2.11/0.66    inference(resolution,[],[f134,f96])).
% 2.11/0.66  fof(f134,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f133,f60])).
% 2.11/0.66  fof(f133,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f131,f62])).
% 2.11/0.66  fof(f131,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(superposition,[],[f80,f63])).
% 2.11/0.66  fof(f80,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f27])).
% 2.11/0.66  fof(f27,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.11/0.66    inference(flattening,[],[f26])).
% 2.11/0.66  fof(f26,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f9])).
% 2.11/0.66  fof(f9,axiom,(
% 2.11/0.66    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 2.11/0.66  fof(f1602,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~spl6_24),
% 2.11/0.66    inference(resolution,[],[f678,f96])).
% 2.11/0.66  fof(f678,plain,(
% 2.11/0.66    ( ! [X2] : (~m1_subset_1(X2,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2)) ) | ~spl6_24),
% 2.11/0.66    inference(subsumption_resolution,[],[f673,f53])).
% 2.11/0.66  fof(f673,plain,(
% 2.11/0.66    ( ! [X2] : (k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),X2) | ~m1_subset_1(X2,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) ) | ~spl6_24),
% 2.11/0.66    inference(resolution,[],[f631,f163])).
% 2.11/0.66  fof(f163,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f162,f60])).
% 2.11/0.66  fof(f162,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f160,f62])).
% 2.11/0.66  fof(f160,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k11_lattice3(k2_yellow_1(X0),X2,X1) = k12_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(superposition,[],[f86,f63])).
% 2.11/0.66  fof(f86,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f29])).
% 2.11/0.66  fof(f29,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 2.11/0.66    inference(flattening,[],[f28])).
% 2.11/0.66  fof(f28,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f8])).
% 2.11/0.66  fof(f8,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 2.11/0.66  fof(f223,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k12_lattice3(X1,X0,X2),X0) | ~r1_tarski(X0,k12_lattice3(X1,X0,X2)) | r3_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~v3_orders_2(X1)) )),
% 2.11/0.66    inference(extensionality_resolution,[],[f85,f78])).
% 2.11/0.66  fof(f78,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f49])).
% 2.11/0.66  fof(f49,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.11/0.66    inference(nnf_transformation,[],[f25])).
% 2.11/0.66  fof(f25,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 2.11/0.66    inference(flattening,[],[f24])).
% 2.11/0.66  fof(f24,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f10])).
% 2.11/0.66  fof(f10,axiom,(
% 2.11/0.66    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).
% 2.11/0.66  fof(f85,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f51])).
% 2.11/0.66  fof(f1636,plain,(
% 2.11/0.66    spl6_2 | ~spl6_24 | ~spl6_29),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f1635])).
% 2.11/0.66  fof(f1635,plain,(
% 2.11/0.66    $false | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1634,f52])).
% 2.11/0.66  fof(f1634,plain,(
% 2.11/0.66    v1_xboole_0(sK2) | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1633,f631])).
% 2.11/0.66  fof(f1633,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (spl6_2 | ~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1632,f107])).
% 2.11/0.66  fof(f107,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | spl6_2),
% 2.11/0.66    inference(avatar_component_clause,[],[f105])).
% 2.11/0.66  fof(f105,plain,(
% 2.11/0.66    spl6_2 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.11/0.66  fof(f1632,plain,(
% 2.11/0.66    r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1630,f95])).
% 2.11/0.66  fof(f95,plain,(
% 2.11/0.66    m1_subset_1(sK4,sK2)),
% 2.11/0.66    inference(backward_demodulation,[],[f55,f63])).
% 2.11/0.66  fof(f55,plain,(
% 2.11/0.66    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))),
% 2.11/0.66    inference(cnf_transformation,[],[f40])).
% 2.11/0.66  fof(f1630,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,sK2) | r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(resolution,[],[f1621,f112])).
% 2.11/0.66  fof(f1621,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1620,f631])).
% 2.11/0.66  fof(f1620,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(forward_demodulation,[],[f1619,f63])).
% 2.11/0.66  fof(f1619,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1618,f95])).
% 2.11/0.66  fof(f1618,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,sK2) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(forward_demodulation,[],[f1617,f63])).
% 2.11/0.66  fof(f1617,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1616,f58])).
% 2.11/0.66  fof(f1616,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1615,f60])).
% 2.11/0.66  fof(f1615,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1614,f53])).
% 2.11/0.66  fof(f1614,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1613,f62])).
% 2.11/0.66  fof(f1613,plain,(
% 2.11/0.66    r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1612,f93])).
% 2.11/0.66  fof(f1612,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1609])).
% 2.11/0.66  fof(f1609,plain,(
% 2.11/0.66    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | r3_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(superposition,[],[f223,f1606])).
% 2.11/0.66  fof(f1606,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | (~spl6_24 | ~spl6_29)),
% 2.11/0.66    inference(forward_demodulation,[],[f1601,f1201])).
% 2.11/0.66  fof(f1201,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_29),
% 2.11/0.66    inference(backward_demodulation,[],[f172,f754])).
% 2.11/0.66  fof(f754,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_29),
% 2.11/0.66    inference(avatar_component_clause,[],[f752])).
% 2.11/0.66  fof(f752,plain,(
% 2.11/0.66    spl6_29 <=> k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.11/0.66  fof(f172,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.11/0.66    inference(resolution,[],[f167,f96])).
% 2.11/0.66  fof(f167,plain,(
% 2.11/0.66    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,sK4),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,sK4))) )),
% 2.11/0.66    inference(resolution,[],[f144,f95])).
% 2.11/0.66  fof(f144,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),X0,X1),sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),X0,X1)) | ~m1_subset_1(X0,sK2)) )),
% 2.11/0.66    inference(resolution,[],[f140,f110])).
% 2.11/0.66  fof(f110,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f109,f62])).
% 2.11/0.66  fof(f109,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 2.11/0.66    inference(superposition,[],[f87,f63])).
% 2.11/0.66  fof(f87,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f31])).
% 2.11/0.66  fof(f31,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 2.11/0.66    inference(flattening,[],[f30])).
% 2.11/0.66  fof(f30,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f6])).
% 2.11/0.66  fof(f6,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 2.11/0.66  fof(f140,plain,(
% 2.11/0.66    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f135,f53])).
% 2.11/0.66  fof(f135,plain,(
% 2.11/0.66    ( ! [X0] : (k11_lattice3(k2_yellow_1(sK2),X0,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,X0) | ~m1_subset_1(X0,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) )),
% 2.11/0.66    inference(resolution,[],[f134,f95])).
% 2.11/0.66  fof(f1601,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) = k12_lattice3(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_24),
% 2.11/0.66    inference(resolution,[],[f678,f95])).
% 2.11/0.66  fof(f1077,plain,(
% 2.11/0.66    ~spl6_3 | ~spl6_24 | spl6_27),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f1076])).
% 2.11/0.66  fof(f1076,plain,(
% 2.11/0.66    $false | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1075,f96])).
% 2.11/0.66  fof(f1075,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,sK2) | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.11/0.66    inference(forward_demodulation,[],[f1074,f63])).
% 2.11/0.66  fof(f1074,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | ~spl6_24 | spl6_27)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1073,f631])).
% 2.11/0.66  fof(f1073,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.11/0.66    inference(forward_demodulation,[],[f1072,f63])).
% 2.11/0.66  fof(f1072,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1071,f95])).
% 2.11/0.66  fof(f1071,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.11/0.66    inference(forward_demodulation,[],[f1070,f63])).
% 2.11/0.66  fof(f1070,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1069,f220])).
% 2.11/0.66  fof(f220,plain,(
% 2.11/0.66    r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~spl6_3),
% 2.11/0.66    inference(resolution,[],[f151,f71])).
% 2.11/0.66  fof(f71,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X2)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f48])).
% 2.11/0.66  fof(f48,plain,(
% 2.11/0.66    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 2.11/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 2.11/0.66  fof(f47,plain,(
% 2.11/0.66    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) => (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.11/0.66    introduced(choice_axiom,[])).
% 2.11/0.66  fof(f46,plain,(
% 2.11/0.66    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 2.11/0.66    inference(rectify,[],[f45])).
% 2.11/0.66  fof(f45,plain,(
% 2.11/0.66    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 2.11/0.66    inference(flattening,[],[f44])).
% 2.11/0.66  fof(f44,plain,(
% 2.11/0.66    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 2.11/0.66    inference(nnf_transformation,[],[f34])).
% 2.11/0.66  fof(f34,plain,(
% 2.11/0.66    ! [X3,X0,X2,X1] : (sP0(X3,X0,X2,X1) <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))),
% 2.11/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.11/0.66  fof(f151,plain,(
% 2.11/0.66    sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4) | ~spl6_3),
% 2.11/0.66    inference(avatar_component_clause,[],[f149])).
% 2.11/0.66  fof(f149,plain,(
% 2.11/0.66    spl6_3 <=> sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.11/0.66  fof(f1069,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | (~spl6_3 | spl6_27)),
% 2.11/0.66    inference(subsumption_resolution,[],[f1068,f221])).
% 2.11/0.66  fof(f221,plain,(
% 2.11/0.66    r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~spl6_3),
% 2.11/0.66    inference(resolution,[],[f151,f70])).
% 2.11/0.66  fof(f70,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X3)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f48])).
% 2.11/0.66  fof(f1068,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.11/0.66    inference(subsumption_resolution,[],[f1067,f60])).
% 2.11/0.66  fof(f1067,plain,(
% 2.11/0.66    ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.11/0.66    inference(subsumption_resolution,[],[f1066,f53])).
% 2.11/0.66  fof(f1066,plain,(
% 2.11/0.66    ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.11/0.66    inference(subsumption_resolution,[],[f1047,f62])).
% 2.11/0.66  fof(f1047,plain,(
% 2.11/0.66    ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | spl6_27),
% 2.11/0.66    inference(resolution,[],[f375,f738])).
% 2.11/0.66  fof(f738,plain,(
% 2.11/0.66    ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | spl6_27),
% 2.11/0.66    inference(avatar_component_clause,[],[f736])).
% 2.11/0.66  fof(f736,plain,(
% 2.11/0.66    spl6_27 <=> r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.11/0.66  fof(f375,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,X3,k11_lattice3(X1,X0,X2)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r1_orders_2(X1,X3,X2) | ~r1_orders_2(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.11/0.66    inference(resolution,[],[f190,f72])).
% 2.11/0.66  fof(f72,plain,(
% 2.11/0.66    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1)) | r1_orders_2(X1,X5,X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f48])).
% 2.11/0.66  fof(f190,plain,(
% 2.11/0.66    ( ! [X6,X4,X5] : (sP0(k11_lattice3(X4,X5,X6),X4,X6,X5) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v2_lattice3(X4) | ~v5_orders_2(X4) | ~m1_subset_1(X6,u1_struct_0(X4))) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f187,f87])).
% 2.11/0.66  fof(f187,plain,(
% 2.11/0.66    ( ! [X6,X4,X5] : (~m1_subset_1(k11_lattice3(X4,X5,X6),u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v2_lattice3(X4) | ~v5_orders_2(X4) | sP0(k11_lattice3(X4,X5,X6),X4,X6,X5)) )),
% 2.11/0.66    inference(resolution,[],[f170,f92])).
% 2.11/0.66  fof(f92,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2,k11_lattice3(X2,X0,X1)) | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0)) )),
% 2.11/0.66    inference(equality_resolution,[],[f68])).
% 2.11/0.66  fof(f68,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f43])).
% 2.11/0.66  fof(f43,plain,(
% 2.11/0.66    ! [X0,X1,X2,X3] : (((k11_lattice3(X2,X0,X1) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3)) | ~sP1(X0,X1,X2,X3))),
% 2.11/0.66    inference(rectify,[],[f42])).
% 2.11/0.66  fof(f42,plain,(
% 2.11/0.66    ! [X1,X2,X0,X3] : (((k11_lattice3(X0,X1,X2) = X3 | ~sP0(X3,X0,X2,X1)) & (sP0(X3,X0,X2,X1) | k11_lattice3(X0,X1,X2) != X3)) | ~sP1(X1,X2,X0,X3))),
% 2.11/0.66    inference(nnf_transformation,[],[f35])).
% 2.11/0.66  fof(f35,plain,(
% 2.11/0.66    ! [X1,X2,X0,X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> sP0(X3,X0,X2,X1)) | ~sP1(X1,X2,X0,X3))),
% 2.11/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.11/0.66  fof(f170,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 2.11/0.66    inference(subsumption_resolution,[],[f77,f67])).
% 2.11/0.66  fof(f67,plain,(
% 2.11/0.66    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f21])).
% 2.11/0.66  fof(f21,plain,(
% 2.11/0.66    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 2.11/0.66    inference(flattening,[],[f20])).
% 2.11/0.66  fof(f20,plain,(
% 2.11/0.66    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 2.11/0.66    inference(ennf_transformation,[],[f5])).
% 2.11/0.66  fof(f5,axiom,(
% 2.11/0.66    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 2.11/0.66  fof(f77,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f36])).
% 2.11/0.66  fof(f36,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.11/0.66    inference(definition_folding,[],[f23,f35,f34])).
% 2.11/0.66  fof(f23,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 2.11/0.66    inference(flattening,[],[f22])).
% 2.11/0.66  fof(f22,plain,(
% 2.11/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 2.11/0.66    inference(ennf_transformation,[],[f7])).
% 2.11/0.66  fof(f7,axiom,(
% 2.11/0.66    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 2.11/0.66  fof(f755,plain,(
% 2.11/0.66    ~spl6_27 | spl6_29 | ~spl6_3 | ~spl6_24),
% 2.11/0.66    inference(avatar_split_clause,[],[f750,f630,f149,f752,f736])).
% 2.11/0.66  fof(f750,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | (~spl6_3 | ~spl6_24)),
% 2.11/0.66    inference(subsumption_resolution,[],[f749,f631])).
% 2.11/0.66  fof(f749,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_3),
% 2.11/0.66    inference(forward_demodulation,[],[f748,f63])).
% 2.11/0.66  fof(f748,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f747,f95])).
% 2.11/0.66  fof(f747,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(forward_demodulation,[],[f746,f63])).
% 2.11/0.66  fof(f746,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f745,f60])).
% 2.11/0.66  fof(f745,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f744,f53])).
% 2.11/0.66  fof(f744,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f716,f62])).
% 2.11/0.66  fof(f716,plain,(
% 2.11/0.66    ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(resolution,[],[f446,f221])).
% 2.11/0.66  fof(f446,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | k11_lattice3(X1,X2,X0) = X0 | ~r1_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f438])).
% 2.11/0.66  fof(f438,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | k11_lattice3(X1,X2,X0) = X0 | ~r1_orders_2(X1,X0,X0) | ~r1_orders_2(X1,X0,X2)) )),
% 2.11/0.66    inference(resolution,[],[f186,f120])).
% 2.11/0.66  fof(f120,plain,(
% 2.11/0.66    ( ! [X4,X5,X3] : (sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f119])).
% 2.11/0.66  fof(f119,plain,(
% 2.11/0.66    ( ! [X4,X5,X3] : (sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5) | sP0(X3,X4,X3,X5) | ~r1_orders_2(X4,X3,X3) | ~r1_orders_2(X4,X3,X5)) )),
% 2.11/0.66    inference(resolution,[],[f76,f75])).
% 2.11/0.66  fof(f75,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) | sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f48])).
% 2.11/0.66  fof(f76,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) | sP0(X0,X1,X2,X3) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f48])).
% 2.11/0.66  fof(f186,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | k11_lattice3(X1,X3,X2) = X0) )),
% 2.11/0.66    inference(resolution,[],[f170,f69])).
% 2.11/0.66  fof(f69,plain,(
% 2.11/0.66    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) = X3) )),
% 2.11/0.66    inference(cnf_transformation,[],[f43])).
% 2.11/0.66  fof(f743,plain,(
% 2.11/0.66    ~spl6_27 | spl6_28 | ~spl6_3 | ~spl6_24),
% 2.11/0.66    inference(avatar_split_clause,[],[f734,f630,f149,f740,f736])).
% 2.11/0.66  fof(f734,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | (~spl6_3 | ~spl6_24)),
% 2.11/0.66    inference(subsumption_resolution,[],[f733,f631])).
% 2.11/0.66  fof(f733,plain,(
% 2.11/0.66    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~spl6_3),
% 2.11/0.66    inference(forward_demodulation,[],[f732,f63])).
% 2.11/0.66  fof(f732,plain,(
% 2.11/0.66    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f731,f96])).
% 2.11/0.66  fof(f731,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,sK2) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(forward_demodulation,[],[f730,f63])).
% 2.11/0.66  fof(f730,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f729,f60])).
% 2.11/0.66  fof(f729,plain,(
% 2.11/0.66    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.66    inference(subsumption_resolution,[],[f728,f53])).
% 2.11/0.68  % (8546)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.11/0.68  fof(f728,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.68    inference(subsumption_resolution,[],[f715,f62])).
% 2.11/0.68  fof(f715,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK3,k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~r1_orders_2(k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~spl6_3),
% 2.11/0.68    inference(resolution,[],[f446,f220])).
% 2.11/0.68  fof(f663,plain,(
% 2.11/0.68    spl6_24),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f662])).
% 2.11/0.68  fof(f662,plain,(
% 2.11/0.68    $false | spl6_24),
% 2.11/0.68    inference(subsumption_resolution,[],[f661,f96])).
% 2.11/0.68  fof(f661,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,sK2) | spl6_24),
% 2.11/0.68    inference(subsumption_resolution,[],[f660,f95])).
% 2.11/0.68  fof(f660,plain,(
% 2.11/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | spl6_24),
% 2.11/0.68    inference(resolution,[],[f632,f110])).
% 2.11/0.68  fof(f632,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_24),
% 2.11/0.68    inference(avatar_component_clause,[],[f630])).
% 2.11/0.68  fof(f218,plain,(
% 2.11/0.68    spl6_4),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f217])).
% 2.11/0.68  fof(f217,plain,(
% 2.11/0.68    $false | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f216,f96])).
% 2.11/0.68  fof(f216,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,sK2) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f215,f95])).
% 2.11/0.68  fof(f215,plain,(
% 2.11/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | spl6_4),
% 2.11/0.68    inference(resolution,[],[f198,f110])).
% 2.11/0.68  fof(f198,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f197,f95])).
% 2.11/0.68  fof(f197,plain,(
% 2.11/0.68    ~m1_subset_1(sK4,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | spl6_4),
% 2.11/0.68    inference(forward_demodulation,[],[f196,f63])).
% 2.11/0.68  fof(f196,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f195,f96])).
% 2.11/0.68  fof(f195,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,sK2) | ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.11/0.68    inference(forward_demodulation,[],[f194,f63])).
% 2.11/0.68  fof(f194,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.11/0.68    inference(forward_demodulation,[],[f193,f63])).
% 2.11/0.68  fof(f193,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f192,f60])).
% 2.11/0.68  fof(f192,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f191,f53])).
% 2.11/0.68  fof(f191,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f188,f62])).
% 2.11/0.68  fof(f188,plain,(
% 2.11/0.68    ~m1_subset_1(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2)) | ~v5_orders_2(k2_yellow_1(sK2)) | spl6_4),
% 2.11/0.68    inference(resolution,[],[f170,f155])).
% 2.11/0.68  fof(f155,plain,(
% 2.11/0.68    ~sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | spl6_4),
% 2.11/0.68    inference(avatar_component_clause,[],[f153])).
% 2.11/0.68  fof(f153,plain,(
% 2.11/0.68    spl6_4 <=> sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.11/0.68  fof(f156,plain,(
% 2.11/0.68    spl6_3 | ~spl6_4),
% 2.11/0.68    inference(avatar_split_clause,[],[f147,f153,f149])).
% 2.11/0.68  fof(f147,plain,(
% 2.11/0.68    ~sP1(sK4,sK3,k2_yellow_1(sK2),k11_lattice3(k2_yellow_1(sK2),sK3,sK4)) | sP0(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK3,sK4)),
% 2.11/0.68    inference(superposition,[],[f92,f143])).
% 2.11/0.68  fof(f143,plain,(
% 2.11/0.68    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3)),
% 2.11/0.68    inference(resolution,[],[f140,f96])).
% 2.11/0.68  fof(f108,plain,(
% 2.11/0.68    ~spl6_1 | ~spl6_2),
% 2.11/0.68    inference(avatar_split_clause,[],[f99,f105,f101])).
% 2.11/0.68  fof(f99,plain,(
% 2.11/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)),
% 2.11/0.68    inference(resolution,[],[f91,f90])).
% 2.11/0.68  fof(f90,plain,(
% 2.11/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))),
% 2.11/0.68    inference(definition_unfolding,[],[f56,f89])).
% 2.11/0.68  fof(f89,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.11/0.68    inference(definition_unfolding,[],[f81,f82])).
% 2.11/0.68  fof(f82,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f3])).
% 2.11/0.68  fof(f3,axiom,(
% 2.11/0.68    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 2.11/0.68  fof(f81,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f4])).
% 2.11/0.68  fof(f4,axiom,(
% 2.11/0.68    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.68  fof(f56,plain,(
% 2.11/0.68    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))),
% 2.11/0.68    inference(cnf_transformation,[],[f40])).
% 2.11/0.68  fof(f91,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.11/0.68    inference(definition_unfolding,[],[f88,f89])).
% 2.11/0.68  fof(f88,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f33])).
% 2.11/0.68  fof(f33,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.11/0.68    inference(flattening,[],[f32])).
% 2.11/0.68  fof(f32,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.11/0.68    inference(ennf_transformation,[],[f2])).
% 2.11/0.68  fof(f2,axiom,(
% 2.11/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.11/0.68  % SZS output end Proof for theBenchmark
% 2.11/0.68  % (8521)------------------------------
% 2.11/0.68  % (8521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (8521)Termination reason: Refutation
% 2.11/0.68  
% 2.11/0.68  % (8521)Memory used [KB]: 11769
% 2.11/0.68  % (8521)Time elapsed: 0.225 s
% 2.11/0.68  % (8521)------------------------------
% 2.11/0.68  % (8521)------------------------------
% 2.11/0.68  % (8514)Success in time 0.306 s
%------------------------------------------------------------------------------

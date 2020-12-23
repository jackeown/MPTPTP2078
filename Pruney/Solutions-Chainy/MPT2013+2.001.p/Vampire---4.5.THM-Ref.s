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
% DateTime   : Thu Dec  3 13:23:02 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 699 expanded)
%              Number of leaves         :    6 ( 121 expanded)
%              Depth                    :   46
%              Number of atoms          :  709 (4123 expanded)
%              Number of equality atoms :   60 ( 497 expanded)
%              Maximal formula depth    :   19 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f259,f18])).

fof(f18,plain,(
    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
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
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f259,plain,(
    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    inference(resolution,[],[f254,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f250,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X0)),a_3_0_waybel_9(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f122,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f121,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f20])).

fof(f20,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) ) ),
    inference(condensation,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1)
      | a_3_0_waybel_9(sK0,sK1,X0) = X1
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) ) ),
    inference(resolution,[],[f110,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(superposition,[],[f104,f80])).

fof(f80,plain,(
    ! [X19,X20,X18] :
      ( sK5(X18,X19,X20) = X20
      | ~ l1_waybel_0(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | v2_struct_0(X18)
      | ~ r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19))) ) ),
    inference(subsumption_resolution,[],[f79,f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0)
      | ~ l1_waybel_0(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0) ) ),
    inference(resolution,[],[f22,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f22,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X19,X20,X18] :
      ( v2_struct_0(X18)
      | ~ l1_waybel_0(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0)
      | sK5(X18,X19,X20) = X20
      | ~ r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19))) ) ),
    inference(subsumption_resolution,[],[f72,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0) ) ),
    inference(resolution,[],[f22,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X19,X20,X18] :
      ( v2_struct_0(X18)
      | ~ l1_waybel_0(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X18,X19),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0)
      | sK5(X18,X19,X20) = X20
      | ~ r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19))) ) ),
    inference(subsumption_resolution,[],[f63,f21])).

fof(f63,plain,(
    ! [X19,X20,X18] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X18)
      | ~ l1_waybel_0(X18,sK0)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X18,X19),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0)
      | sK5(X18,X19,X20) = X20
      | ~ r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19))) ) ),
    inference(resolution,[],[f22,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
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
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f104,plain,(
    ! [X17,X15,X16] :
      ( r1_orders_2(X15,X16,sK5(X15,X16,X17))
      | ~ l1_waybel_0(X15,sK0)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | v2_struct_0(X15)
      | ~ r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16))) ) ),
    inference(subsumption_resolution,[],[f103,f66])).

fof(f103,plain,(
    ! [X17,X15,X16] :
      ( v2_struct_0(X15)
      | ~ l1_waybel_0(X15,sK0)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0)
      | r1_orders_2(X15,X16,sK5(X15,X16,X17))
      | ~ r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16))) ) ),
    inference(subsumption_resolution,[],[f71,f65])).

fof(f71,plain,(
    ! [X17,X15,X16] :
      ( v2_struct_0(X15)
      | ~ l1_waybel_0(X15,sK0)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X15,X16),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0)
      | r1_orders_2(X15,X16,sK5(X15,X16,X17))
      | ~ r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16))) ) ),
    inference(subsumption_resolution,[],[f62,f21])).

fof(f62,plain,(
    ! [X17,X15,X16] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X15)
      | ~ l1_waybel_0(X15,sK0)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X15,X16),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0)
      | r1_orders_2(X15,X16,sK5(X15,X16,X17))
      | ~ r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16))) ) ),
    inference(resolution,[],[f22,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK5(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | r1_orders_2(X1,X2,sK5(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK1,X1,sK6(X0,a_3_0_waybel_9(sK0,sK1,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X0,a_3_0_waybel_9(sK0,sK1,X1)),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,X1),X0)
      | a_3_0_waybel_9(sK0,sK1,X1) = X0 ) ),
    inference(resolution,[],[f102,f35])).

fof(f102,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6))
      | ~ r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4)))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)))
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f101,f19])).

fof(f101,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4)))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)))
      | v2_struct_0(sK1)
      | r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6)) ) ),
    inference(subsumption_resolution,[],[f99,f20])).

fof(f99,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4)))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)))
      | v2_struct_0(sK1)
      | r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6)) ) ),
    inference(resolution,[],[f97,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X2,a_3_0_waybel_9(sK0,X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ r1_orders_2(X0,X1,sK6(X2,a_3_0_waybel_9(sK0,X0,X1)))
      | v2_struct_0(X0)
      | r1_tarski(X2,a_3_0_waybel_9(sK0,X0,X1)) ) ),
    inference(resolution,[],[f73,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X23,X21,X22] :
      ( r2_hidden(X23,a_3_0_waybel_9(sK0,X21,X22))
      | ~ l1_waybel_0(X21,sK0)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | ~ r1_orders_2(X21,X22,X23)
      | v2_struct_0(X21) ) ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f64,plain,(
    ! [X23,X21,X22] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X21)
      | ~ l1_waybel_0(X21,sK0)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | ~ r1_orders_2(X21,X22,X23)
      | r2_hidden(X23,a_3_0_waybel_9(sK0,X21,X22)) ) ),
    inference(resolution,[],[f22,f55])).

fof(f55,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | X0 != X4
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f95,f19])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,X1))) ) ),
    inference(resolution,[],[f94,f20])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,sK0)
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2)))
      | ~ l1_waybel_0(X1,sK0)
      | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2))) ) ),
    inference(resolution,[],[f84,f22])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X3)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1)))
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_waybel_0(k4_waybel_9(X3,X0,X1),X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1)))
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_waybel_0(k4_waybel_9(X3,X0,X1),X3)
      | ~ l1_waybel_0(k4_waybel_9(X3,X0,X1),X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1)))
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_waybel_0(k4_waybel_9(X3,X0,X1),X3)
      | ~ l1_waybel_0(k4_waybel_9(X3,X0,X1),X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1)))
      | ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) ) ),
    inference(superposition,[],[f52,f80])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f250,plain,(
    ! [X0] :
      ( u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) ) ),
    inference(resolution,[],[f249,f37])).

fof(f249,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f248,f19])).

fof(f248,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f244,f20])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0)) ) ),
    inference(condensation,[],[f242])).

fof(f242,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3))
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X2)) ) ),
    inference(resolution,[],[f154,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,X2,X0)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,X2,X0)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(superposition,[],[f68,f67])).

fof(f67,plain,(
    ! [X6,X4,X5] :
      ( sK7(X6,X4,X5) = X6
      | ~ l1_waybel_0(X4,sK0)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ r2_hidden(X6,a_3_0_waybel_9(sK0,X4,X5)) ) ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f58,plain,(
    ! [X6,X4,X5] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X4)
      | ~ l1_waybel_0(X4,sK0)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | sK7(X6,X4,X5) = X6
      | ~ r2_hidden(X6,a_3_0_waybel_9(sK0,X4,X5)) ) ),
    inference(resolution,[],[f22,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | sK7(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X8,X7,X9] :
      ( r1_orders_2(X7,X8,sK7(X9,X7,X8))
      | ~ l1_waybel_0(X7,sK0)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | v2_struct_0(X7)
      | ~ r2_hidden(X9,a_3_0_waybel_9(sK0,X7,X8)) ) ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f59,plain,(
    ! [X8,X7,X9] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X7)
      | ~ l1_waybel_0(X7,sK0)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | r1_orders_2(X7,X8,sK7(X9,X7,X8))
      | ~ r2_hidden(X9,a_3_0_waybel_9(sK0,X7,X8)) ) ),
    inference(resolution,[],[f22,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_orders_2(X2,X3,sK7(X0,X2,X3))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3)) ) ),
    inference(subsumption_resolution,[],[f153,f20])).

fof(f153,plain,(
    ! [X2,X3] :
      ( u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3)) ) ),
    inference(subsumption_resolution,[],[f152,f19])).

fof(f152,plain,(
    ! [X2,X3] :
      ( u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3)) ) ),
    inference(resolution,[],[f135,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f86,f21])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))
      | ~ l1_waybel_0(X1,sK0)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(resolution,[],[f75,f22])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X3)
      | ~ r2_hidden(X0,a_3_0_waybel_9(X3,X1,X2))
      | ~ l1_waybel_0(X1,sK0)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X3)
      | ~ r2_hidden(X0,a_3_0_waybel_9(X3,X1,X2))
      | ~ l1_waybel_0(X1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) ) ),
    inference(superposition,[],[f41,f67])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X2,X3),u1_struct_0(X2))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) ) ),
    inference(subsumption_resolution,[],[f134,f20])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))))
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f133,f19])).

fof(f133,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))))
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,sK0) ) ),
    inference(resolution,[],[f129,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,sK6(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f108,f38])).

fof(f108,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13)))
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r1_orders_2(X12,X13,X14)
      | v2_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f107,f66])).

fof(f107,plain,(
    ! [X14,X12,X13] :
      ( v2_struct_0(X12)
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r1_orders_2(X12,X13,X14)
      | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13))) ) ),
    inference(subsumption_resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X14,X12,X13] :
      ( v2_struct_0(X12)
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X12,X13),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r1_orders_2(X12,X13,X14)
      | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13))) ) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f61,plain,(
    ! [X14,X12,X13] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X12)
      | ~ l1_waybel_0(X12,sK0)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ v6_waybel_0(k4_waybel_9(sK0,X12,X13),sK0)
      | ~ l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r1_orders_2(X12,X13,X14)
      | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13))) ) ),
    inference(resolution,[],[f22,f49])).

fof(f49,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X4 != X5
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f11])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (21296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (21288)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (21290)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (21290)Refutation not found, incomplete strategy% (21290)------------------------------
% 0.21/0.51  % (21290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21315)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (21289)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (21299)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21293)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (21290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  % (21292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (21298)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  
% 0.21/0.52  % (21290)Memory used [KB]: 10746
% 0.21/0.52  % (21290)Time elapsed: 0.109 s
% 0.21/0.52  % (21290)------------------------------
% 0.21/0.52  % (21290)------------------------------
% 0.21/0.52  % (21297)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (21310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  % (21312)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.53  % (21295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.53  % (21304)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.53  % (21303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (21291)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (21294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (21302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (21316)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.54  % (21311)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.54  % (21317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (21309)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.55  % (21314)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (21313)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (21308)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (21310)Refutation not found, incomplete strategy% (21310)------------------------------
% 1.43/0.55  % (21310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (21310)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (21310)Memory used [KB]: 10874
% 1.43/0.55  % (21310)Time elapsed: 0.150 s
% 1.43/0.55  % (21310)------------------------------
% 1.43/0.55  % (21310)------------------------------
% 1.43/0.55  % (21307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (21301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.55  % (21314)Refutation not found, incomplete strategy% (21314)------------------------------
% 1.43/0.55  % (21314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (21314)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (21314)Memory used [KB]: 11001
% 1.43/0.55  % (21314)Time elapsed: 0.155 s
% 1.43/0.55  % (21314)------------------------------
% 1.43/0.55  % (21314)------------------------------
% 1.43/0.55  % (21305)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (21306)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (21300)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (21305)Refutation not found, incomplete strategy% (21305)------------------------------
% 1.43/0.56  % (21305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (21305)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (21305)Memory used [KB]: 10618
% 1.43/0.56  % (21305)Time elapsed: 0.151 s
% 1.43/0.56  % (21305)------------------------------
% 1.43/0.56  % (21305)------------------------------
% 1.43/0.58  % (21309)Refutation found. Thanks to Tanya!
% 1.43/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f265,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(subsumption_resolution,[],[f259,f18])).
% 1.43/0.58  fof(f18,plain,(
% 1.43/0.58    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2)),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,plain,(
% 1.43/0.58    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f8])).
% 1.43/0.58  fof(f8,plain,(
% 1.43/0.58    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f7])).
% 1.43/0.58  fof(f7,negated_conjecture,(
% 1.43/0.58    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 1.43/0.58    inference(negated_conjecture,[],[f6])).
% 1.43/0.58  fof(f6,conjecture,(
% 1.43/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).
% 1.43/0.58  fof(f259,plain,(
% 1.43/0.58    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)),
% 1.43/0.58    inference(resolution,[],[f254,f17])).
% 1.43/0.58  fof(f17,plain,(
% 1.43/0.58    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f254,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f250,f129])).
% 1.43/0.58  fof(f129,plain,(
% 1.43/0.58    ( ! [X0] : (~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f125,f35])).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f2])).
% 1.43/0.58  fof(f2,axiom,(
% 1.43/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.58  fof(f125,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X0)),a_3_0_waybel_9(sK0,sK1,X0))) )),
% 1.43/0.58    inference(resolution,[],[f122,f37])).
% 1.43/0.58  fof(f37,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,plain,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f1])).
% 1.43/0.58  fof(f1,axiom,(
% 1.43/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.58  fof(f122,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f121,f19])).
% 1.43/0.58  fof(f19,plain,(
% 1.43/0.58    ~v2_struct_0(sK1)),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f121,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1 | v2_struct_0(sK1)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f120,f20])).
% 1.43/0.58  fof(f20,plain,(
% 1.43/0.58    l1_waybel_0(sK1,sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f120,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1 | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1)) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f119])).
% 1.43/0.58  fof(f119,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0))) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1 | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) )),
% 1.43/0.58    inference(condensation,[],[f118])).
% 1.43/0.58  fof(f118,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1 | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f115])).
% 1.43/0.58  fof(f115,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),X1) | a_3_0_waybel_9(sK0,sK1,X0) = X1 | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK6(X1,a_3_0_waybel_9(sK0,sK1,X0)),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) )),
% 1.43/0.58    inference(resolution,[],[f110,f106])).
% 1.43/0.58  fof(f106,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f105])).
% 1.43/0.58  fof(f105,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(superposition,[],[f104,f80])).
% 1.43/0.58  fof(f80,plain,(
% 1.43/0.58    ( ! [X19,X20,X18] : (sK5(X18,X19,X20) = X20 | ~l1_waybel_0(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(X18)) | v2_struct_0(X18) | ~r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f79,f66])).
% 1.43/0.58  fof(f66,plain,(
% 1.43/0.58    ( ! [X2,X3] : (l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X2)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f57,f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    ~v2_struct_0(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f57,plain,(
% 1.43/0.58    ( ! [X2,X3] : (v2_struct_0(sK0) | v2_struct_0(X2) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(X2)) | l1_waybel_0(k4_waybel_9(sK0,X2,X3),sK0)) )),
% 1.43/0.58    inference(resolution,[],[f22,f40])).
% 1.43/0.58  fof(f40,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f14])).
% 1.43/0.58  fof(f14,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f13])).
% 1.43/0.58  fof(f13,plain,(
% 1.43/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f4])).
% 1.43/0.58  fof(f4,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    l1_struct_0(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f9])).
% 1.43/0.58  fof(f79,plain,(
% 1.43/0.58    ( ! [X19,X20,X18] : (v2_struct_0(X18) | ~l1_waybel_0(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(X18)) | ~l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0) | sK5(X18,X19,X20) = X20 | ~r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f72,f65])).
% 1.43/0.58  fof(f65,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f56,f21])).
% 1.43/0.58  fof(f56,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v6_waybel_0(k4_waybel_9(sK0,X0,X1),sK0)) )),
% 1.43/0.58    inference(resolution,[],[f22,f39])).
% 1.43/0.58  fof(f39,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f14])).
% 1.43/0.58  fof(f72,plain,(
% 1.43/0.58    ( ! [X19,X20,X18] : (v2_struct_0(X18) | ~l1_waybel_0(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(X18)) | ~v6_waybel_0(k4_waybel_9(sK0,X18,X19),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0) | sK5(X18,X19,X20) = X20 | ~r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f63,f21])).
% 1.43/0.58  fof(f63,plain,(
% 1.43/0.58    ( ! [X19,X20,X18] : (v2_struct_0(sK0) | v2_struct_0(X18) | ~l1_waybel_0(X18,sK0) | ~m1_subset_1(X19,u1_struct_0(X18)) | ~v6_waybel_0(k4_waybel_9(sK0,X18,X19),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X18,X19),sK0) | sK5(X18,X19,X20) = X20 | ~r2_hidden(X20,u1_struct_0(k4_waybel_9(sK0,X18,X19)))) )),
% 1.43/0.58    inference(resolution,[],[f22,f51])).
% 1.43/0.58  fof(f51,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | sK5(X1,X2,X4) = X4 | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 1.43/0.58    inference(equality_resolution,[],[f24])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | sK5(X1,X2,X4) = X4 | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(cnf_transformation,[],[f11])).
% 1.43/0.58  fof(f11,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f10])).
% 1.43/0.58  fof(f10,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).
% 1.43/0.58  fof(f104,plain,(
% 1.43/0.58    ( ! [X17,X15,X16] : (r1_orders_2(X15,X16,sK5(X15,X16,X17)) | ~l1_waybel_0(X15,sK0) | ~m1_subset_1(X16,u1_struct_0(X15)) | v2_struct_0(X15) | ~r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f103,f66])).
% 1.43/0.58  fof(f103,plain,(
% 1.43/0.58    ( ! [X17,X15,X16] : (v2_struct_0(X15) | ~l1_waybel_0(X15,sK0) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0) | r1_orders_2(X15,X16,sK5(X15,X16,X17)) | ~r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f71,f65])).
% 1.43/0.58  fof(f71,plain,(
% 1.43/0.58    ( ! [X17,X15,X16] : (v2_struct_0(X15) | ~l1_waybel_0(X15,sK0) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~v6_waybel_0(k4_waybel_9(sK0,X15,X16),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0) | r1_orders_2(X15,X16,sK5(X15,X16,X17)) | ~r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f62,f21])).
% 1.43/0.58  fof(f62,plain,(
% 1.43/0.58    ( ! [X17,X15,X16] : (v2_struct_0(sK0) | v2_struct_0(X15) | ~l1_waybel_0(X15,sK0) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~v6_waybel_0(k4_waybel_9(sK0,X15,X16),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X15,X16),sK0) | r1_orders_2(X15,X16,sK5(X15,X16,X17)) | ~r2_hidden(X17,u1_struct_0(k4_waybel_9(sK0,X15,X16)))) )),
% 1.43/0.58    inference(resolution,[],[f22,f50])).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | r1_orders_2(X1,X2,sK5(X1,X2,X4)) | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 1.43/0.58    inference(equality_resolution,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | r1_orders_2(X1,X2,sK5(X1,X2,X4)) | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(cnf_transformation,[],[f11])).
% 1.43/0.58  fof(f110,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~r1_orders_2(sK1,X1,sK6(X0,a_3_0_waybel_9(sK0,sK1,X1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(sK6(X0,a_3_0_waybel_9(sK0,sK1,X1)),u1_struct_0(k4_waybel_9(sK0,sK1,X2))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r1_tarski(a_3_0_waybel_9(sK0,sK1,X1),X0) | a_3_0_waybel_9(sK0,sK1,X1) = X0) )),
% 1.43/0.58    inference(resolution,[],[f102,f35])).
% 1.43/0.58  fof(f102,plain,(
% 1.43/0.58    ( ! [X6,X4,X5] : (r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6)) | ~r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4))) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6))) | ~m1_subset_1(X4,u1_struct_0(sK1))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f101,f19])).
% 1.43/0.58  fof(f101,plain,(
% 1.43/0.58    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK1)) | ~r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4))) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6))) | v2_struct_0(sK1) | r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f99,f20])).
% 1.43/0.58  fof(f99,plain,(
% 1.43/0.58    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK1)) | ~r2_hidden(sK6(X5,a_3_0_waybel_9(sK0,sK1,X6)),u1_struct_0(k4_waybel_9(sK0,sK1,X4))) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~r1_orders_2(sK1,X6,sK6(X5,a_3_0_waybel_9(sK0,sK1,X6))) | v2_struct_0(sK1) | r1_tarski(X5,a_3_0_waybel_9(sK0,sK1,X6))) )),
% 1.43/0.58    inference(resolution,[],[f97,f78])).
% 1.43/0.58  fof(f78,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X2,a_3_0_waybel_9(sK0,X0,X1)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(X0,sK0) | ~r1_orders_2(X0,X1,sK6(X2,a_3_0_waybel_9(sK0,X0,X1))) | v2_struct_0(X0) | r1_tarski(X2,a_3_0_waybel_9(sK0,X0,X1))) )),
% 1.43/0.58    inference(resolution,[],[f73,f38])).
% 1.43/0.58  fof(f38,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f12])).
% 1.43/0.58  fof(f73,plain,(
% 1.43/0.58    ( ! [X23,X21,X22] : (r2_hidden(X23,a_3_0_waybel_9(sK0,X21,X22)) | ~l1_waybel_0(X21,sK0) | ~m1_subset_1(X22,u1_struct_0(X21)) | ~m1_subset_1(X23,u1_struct_0(X21)) | ~r1_orders_2(X21,X22,X23) | v2_struct_0(X21)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f64,f21])).
% 1.43/0.58  fof(f64,plain,(
% 1.43/0.58    ( ! [X23,X21,X22] : (v2_struct_0(sK0) | v2_struct_0(X21) | ~l1_waybel_0(X21,sK0) | ~m1_subset_1(X22,u1_struct_0(X21)) | ~m1_subset_1(X23,u1_struct_0(X21)) | ~r1_orders_2(X21,X22,X23) | r2_hidden(X23,a_3_0_waybel_9(sK0,X21,X22))) )),
% 1.43/0.58    inference(resolution,[],[f22,f55])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X4,X2,X3,X1] : (~l1_struct_0(X1) | v2_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~r1_orders_2(X2,X3,X4) | r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3))) )),
% 1.43/0.58    inference(equality_resolution,[],[f44])).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X1) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X2)) | X0 != X4 | ~r1_orders_2(X2,X3,X4) | r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f16])).
% 1.43/0.58  fof(f16,plain,(
% 1.43/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 1.43/0.58    inference(flattening,[],[f15])).
% 1.43/0.58  fof(f15,plain,(
% 1.43/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 1.43/0.58    inference(ennf_transformation,[],[f5])).
% 1.43/0.58  fof(f5,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).
% 1.43/0.58  fof(f97,plain,(
% 1.43/0.58    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,X1)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f95,f19])).
% 1.43/0.58  fof(f95,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v2_struct_0(sK1) | m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,X1)))) )),
% 1.43/0.58    inference(resolution,[],[f94,f20])).
% 1.43/0.58  fof(f94,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,sK0) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f93,f21])).
% 1.43/0.58  fof(f93,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(sK0) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2)))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f92])).
% 1.43/0.58  fof(f92,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(sK0) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2))) | ~l1_waybel_0(X1,sK0) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,X1,X2)))) )),
% 1.43/0.58    inference(resolution,[],[f84,f22])).
% 1.43/0.58  fof(f84,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X3) | m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_waybel_0(X0,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X3) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1))) | ~l1_waybel_0(X0,sK0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f83,f40])).
% 1.43/0.58  fof(f83,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_struct_0(X3) | v2_struct_0(X0) | ~l1_waybel_0(X0,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_waybel_0(k4_waybel_9(X3,X0,X1),X3) | v2_struct_0(X3) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1))) | ~l1_waybel_0(X0,sK0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f82,f39])).
% 1.43/0.58  fof(f82,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_struct_0(X3) | v2_struct_0(X0) | ~l1_waybel_0(X0,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_waybel_0(k4_waybel_9(X3,X0,X1),X3) | ~l1_waybel_0(k4_waybel_9(X3,X0,X1),X3) | v2_struct_0(X3) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1))) | ~l1_waybel_0(X0,sK0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f81])).
% 1.43/0.58  fof(f81,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_struct_0(X3) | v2_struct_0(X0) | ~l1_waybel_0(X0,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_waybel_0(k4_waybel_9(X3,X0,X1),X3) | ~l1_waybel_0(k4_waybel_9(X3,X0,X1),X3) | v2_struct_0(X3) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(X3,X0,X1))) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) )),
% 1.43/0.58    inference(superposition,[],[f52,f80])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X1] : (m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | v2_struct_0(X0) | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 1.43/0.58    inference(equality_resolution,[],[f23])).
% 1.43/0.58  fof(f23,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1)) | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(cnf_transformation,[],[f11])).
% 1.43/0.58  fof(f250,plain,(
% 1.43/0.58    ( ! [X0] : (u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tarski(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) )),
% 1.43/0.58    inference(resolution,[],[f249,f37])).
% 1.43/0.58  fof(f249,plain,(
% 1.43/0.58    ( ! [X0] : (~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f248,f19])).
% 1.43/0.58  fof(f248,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0)) | v2_struct_0(sK1)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f244,f20])).
% 1.43/0.58  fof(f244,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1)) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f243])).
% 1.43/0.58  fof(f243,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),a_3_0_waybel_9(sK0,sK1,X0))) )),
% 1.43/0.58    inference(condensation,[],[f242])).
% 1.43/0.58  fof(f242,plain,(
% 1.43/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X2))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f241])).
% 1.43/0.58  fof(f241,plain,(
% 1.43/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X2))) )),
% 1.43/0.58    inference(resolution,[],[f154,f77])).
% 1.43/0.58  fof(f77,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r1_orders_2(X1,X2,X0) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f76])).
% 1.43/0.58  fof(f76,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r1_orders_2(X1,X2,X0) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(superposition,[],[f68,f67])).
% 1.43/0.58  fof(f67,plain,(
% 1.43/0.58    ( ! [X6,X4,X5] : (sK7(X6,X4,X5) = X6 | ~l1_waybel_0(X4,sK0) | ~m1_subset_1(X5,u1_struct_0(X4)) | v2_struct_0(X4) | ~r2_hidden(X6,a_3_0_waybel_9(sK0,X4,X5))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f58,f21])).
% 1.43/0.58  fof(f58,plain,(
% 1.43/0.58    ( ! [X6,X4,X5] : (v2_struct_0(sK0) | v2_struct_0(X4) | ~l1_waybel_0(X4,sK0) | ~m1_subset_1(X5,u1_struct_0(X4)) | sK7(X6,X4,X5) = X6 | ~r2_hidden(X6,a_3_0_waybel_9(sK0,X4,X5))) )),
% 1.43/0.58    inference(resolution,[],[f22,f42])).
% 1.43/0.58  fof(f42,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X1) | v2_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | sK7(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f16])).
% 1.43/0.58  fof(f68,plain,(
% 1.43/0.58    ( ! [X8,X7,X9] : (r1_orders_2(X7,X8,sK7(X9,X7,X8)) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | v2_struct_0(X7) | ~r2_hidden(X9,a_3_0_waybel_9(sK0,X7,X8))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f59,f21])).
% 1.43/0.58  fof(f59,plain,(
% 1.43/0.58    ( ! [X8,X7,X9] : (v2_struct_0(sK0) | v2_struct_0(X7) | ~l1_waybel_0(X7,sK0) | ~m1_subset_1(X8,u1_struct_0(X7)) | r1_orders_2(X7,X8,sK7(X9,X7,X8)) | ~r2_hidden(X9,a_3_0_waybel_9(sK0,X7,X8))) )),
% 1.43/0.58    inference(resolution,[],[f22,f43])).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X1) | v2_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_orders_2(X2,X3,sK7(X0,X2,X3)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f16])).
% 1.43/0.58  fof(f154,plain,(
% 1.43/0.58    ( ! [X2,X3] : (~r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f153,f20])).
% 1.43/0.58  fof(f153,plain,(
% 1.43/0.58    ( ! [X2,X3] : (u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f152,f19])).
% 1.43/0.58  fof(f152,plain,(
% 1.43/0.58    ( ! [X2,X3] : (u1_struct_0(k4_waybel_9(sK0,sK1,X2)) = a_3_0_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r1_orders_2(sK1,X2,sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2)))) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_hidden(sK6(a_3_0_waybel_9(sK0,sK1,X2),u1_struct_0(k4_waybel_9(sK0,sK1,X2))),a_3_0_waybel_9(sK0,sK1,X3))) )),
% 1.43/0.58    inference(resolution,[],[f135,f87])).
% 1.43/0.58  fof(f87,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f86,f21])).
% 1.43/0.58  fof(f86,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(sK0) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f85])).
% 1.43/0.58  fof(f85,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(sK0) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2)) | ~l1_waybel_0(X1,sK0) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(resolution,[],[f75,f22])).
% 1.43/0.58  fof(f75,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X3) | m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_waybel_0(X1,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X3) | ~r2_hidden(X0,a_3_0_waybel_9(X3,X1,X2)) | ~l1_waybel_0(X1,sK0) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f74])).
% 1.43/0.58  fof(f74,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,u1_struct_0(X1)) | ~l1_struct_0(X3) | v2_struct_0(X1) | ~l1_waybel_0(X1,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X3) | ~r2_hidden(X0,a_3_0_waybel_9(X3,X1,X2)) | ~l1_waybel_0(X1,sK0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_0_waybel_9(sK0,X1,X2))) )),
% 1.43/0.58    inference(superposition,[],[f41,f67])).
% 1.43/0.58  fof(f41,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X2,X3),u1_struct_0(X2)) | ~l1_struct_0(X1) | v2_struct_0(X2) | ~l1_waybel_0(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X1) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f16])).
% 1.43/0.58  fof(f135,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f134,f20])).
% 1.43/0.58  fof(f134,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1)) | ~r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) | ~l1_waybel_0(sK1,sK0)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f133,f19])).
% 1.43/0.58  fof(f133,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1)) | ~r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0)) )),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f132])).
% 1.43/0.58  fof(f132,plain,(
% 1.43/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | u1_struct_0(k4_waybel_9(sK0,sK1,X0)) = a_3_0_waybel_9(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0))),u1_struct_0(sK1)) | ~r1_orders_2(sK1,X0,sK6(a_3_0_waybel_9(sK0,sK1,X0),u1_struct_0(k4_waybel_9(sK0,sK1,X0)))) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0)) )),
% 1.43/0.58    inference(resolution,[],[f129,f109])).
% 1.43/0.58  fof(f109,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (r1_tarski(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK6(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1))),u1_struct_0(X0)) | ~r1_orders_2(X0,X1,sK6(X2,u1_struct_0(k4_waybel_9(sK0,X0,X1)))) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0)) )),
% 1.43/0.58    inference(resolution,[],[f108,f38])).
% 1.43/0.58  fof(f108,plain,(
% 1.43/0.58    ( ! [X14,X12,X13] : (r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13))) | ~l1_waybel_0(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~m1_subset_1(X14,u1_struct_0(X12)) | ~r1_orders_2(X12,X13,X14) | v2_struct_0(X12)) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f107,f66])).
% 1.43/0.58  fof(f107,plain,(
% 1.43/0.58    ( ! [X14,X12,X13] : (v2_struct_0(X12) | ~l1_waybel_0(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0) | ~m1_subset_1(X14,u1_struct_0(X12)) | ~r1_orders_2(X12,X13,X14) | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f70,f65])).
% 1.43/0.58  fof(f70,plain,(
% 1.43/0.58    ( ! [X14,X12,X13] : (v2_struct_0(X12) | ~l1_waybel_0(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~v6_waybel_0(k4_waybel_9(sK0,X12,X13),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0) | ~m1_subset_1(X14,u1_struct_0(X12)) | ~r1_orders_2(X12,X13,X14) | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13)))) )),
% 1.43/0.58    inference(subsumption_resolution,[],[f61,f21])).
% 1.43/0.58  fof(f61,plain,(
% 1.43/0.58    ( ! [X14,X12,X13] : (v2_struct_0(sK0) | v2_struct_0(X12) | ~l1_waybel_0(X12,sK0) | ~m1_subset_1(X13,u1_struct_0(X12)) | ~v6_waybel_0(k4_waybel_9(sK0,X12,X13),sK0) | ~l1_waybel_0(k4_waybel_9(sK0,X12,X13),sK0) | ~m1_subset_1(X14,u1_struct_0(X12)) | ~r1_orders_2(X12,X13,X14) | r2_hidden(X14,u1_struct_0(k4_waybel_9(sK0,X12,X13)))) )),
% 1.43/0.58    inference(resolution,[],[f22,f49])).
% 1.43/0.58  fof(f49,plain,(
% 1.43/0.58    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X1,X2,X5) | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 1.43/0.58    inference(equality_resolution,[],[f48])).
% 1.43/0.58  fof(f48,plain,(
% 1.43/0.58    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X1,X2,X5) | r2_hidden(X5,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(equality_resolution,[],[f26])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | X4 != X5 | ~r1_orders_2(X1,X2,X5) | r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(cnf_transformation,[],[f11])).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (21309)------------------------------
% 1.43/0.58  % (21309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (21309)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (21309)Memory used [KB]: 1918
% 1.43/0.58  % (21309)Time elapsed: 0.160 s
% 1.43/0.58  % (21309)------------------------------
% 1.43/0.58  % (21309)------------------------------
% 1.43/0.59  % (21287)Success in time 0.222 s
%------------------------------------------------------------------------------

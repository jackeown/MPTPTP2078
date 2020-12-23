%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 625 expanded)
%              Number of leaves         :   20 ( 171 expanded)
%              Depth                    :   90
%              Number of atoms          : 1003 (3544 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f57])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)))
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)))
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f217,plain,(
    ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f216,f59])).

fof(f59,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f216,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f215,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f215,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f214,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f214,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f213,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f213,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK1) ) ),
    inference(resolution,[],[f211,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v7_waybel_0(sK2(X0))
        & v4_orders_2(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & l1_waybel_0(sK2(X0),X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
     => ( v7_waybel_0(sK2(X0))
        & v4_orders_2(sK2(X0))
        & ~ v2_struct_0(sK2(X0))
        & l1_waybel_0(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK2(sK1),X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK1,X1)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f210,f63])).

fof(f210,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK2(sK1),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f208,f62])).

fof(f208,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK2(sK1),X0) ) ),
    inference(resolution,[],[f203,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f203,plain,(
    ! [X0] :
      ( v2_struct_0(sK2(sK1))
      | ~ l1_waybel_0(sK2(sK1),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f202,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).

fof(f202,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK2(sK1))) ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f201,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f57])).

fof(f200,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f199,f59])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f194,f58])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ l1_waybel_0(sK1,X1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f193,f82])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1))) ) ),
    inference(subsumption_resolution,[],[f192,f56])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f57])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK2(sK0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ l1_waybel_0(sK2(sK0),X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f182,f65])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ l1_waybel_0(sK2(sK0),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f181,f82])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1))) ) ),
    inference(subsumption_resolution,[],[f180,f57])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK0)))
      | ~ l1_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK0)))
      | ~ l1_struct_0(sK0)
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f178,f64])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f177,f65])).

fof(f177,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(sK2(X0)) ) ),
    inference(subsumption_resolution,[],[f176,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v4_orders_2(sK2(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | ~ v4_orders_2(sK2(X0))
      | v2_struct_0(sK2(X0)) ) ),
    inference(subsumption_resolution,[],[f175,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v7_waybel_0(sK2(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_waybel_0(sK2(X0))
      | ~ v4_orders_2(sK2(X0))
      | v2_struct_0(sK2(X0)) ) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_waybel_0(sK2(X0))
      | ~ v4_orders_2(sK2(X0))
      | v2_struct_0(sK2(X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f57])).

fof(f173,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_waybel_0(sK2(X0))
      | ~ v4_orders_2(sK2(X0))
      | v2_struct_0(sK2(X0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK2(X0),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(sK2(X0),sK0)
      | ~ v7_waybel_0(sK2(X0))
      | ~ v4_orders_2(sK2(X0))
      | v2_struct_0(sK2(X0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f171,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,u1_struct_0(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,u1_struct_0(X0))
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0))
      | ~ l1_waybel_0(sK2(X1),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X1)))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK2(X1),sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X1)))
      | ~ v4_orders_2(sK2(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f169,f65])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK2(X1),sK0)
      | v2_struct_0(sK2(X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK2(X1)))
      | ~ v4_orders_2(sK2(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f167,f67])).

fof(f167,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ v7_waybel_0(X6)
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_waybel_0(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ v4_orders_2(X6) ) ),
    inference(subsumption_resolution,[],[f166,f56])).

fof(f166,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_waybel_0(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,X6,u1_struct_0(sK0))
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f163,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_waybel_0(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,X6,u1_struct_0(sK0))
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(sK1))
      | ~ l1_waybel_0(X6,sK0)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK0,X6,u1_struct_0(sK0))
      | ~ l1_waybel_0(X6,sK0)
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(X6)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f160,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_waybel_0(sK0,X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_waybel_0(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK2(sK1))) ) ),
    inference(subsumption_resolution,[],[f158,f56])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ r2_waybel_0(sK0,X2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK2(sK1)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f149,f57])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_struct_0(X4)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ r2_waybel_0(X4,X3,u1_struct_0(sK0))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f148,f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
                      & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
        & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f147,f57])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f146,f59])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f145,f63])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1))) ) ),
    inference(resolution,[],[f144,f62])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK2(sK1)) ) ),
    inference(subsumption_resolution,[],[f142,f66])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f67])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1)) ) ),
    inference(subsumption_resolution,[],[f140,f64])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK2(sK1),sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1)) ) ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK2(sK1),sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | v2_struct_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(sK2(sK1),sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f137,f68])).

fof(f137,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ l1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f136,f65])).

fof(f136,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f135,f66])).

fof(f135,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f134,f67])).

fof(f134,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f133,f64])).

fof(f133,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK2(sK1),sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f131,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK1))
      | ~ m1_subset_1(X6,u1_struct_0(sK2(sK1)))
      | ~ r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK2(sK1),sK1)
      | ~ v7_waybel_0(sK2(sK1))
      | ~ v4_orders_2(sK2(sK1))
      | v2_struct_0(sK2(sK1))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f129,f69])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1))) ) ),
    inference(subsumption_resolution,[],[f128,f57])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ l1_struct_0(sK0) ) ),
    inference(resolution,[],[f127,f59])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(sK1,X3)
      | ~ m1_subset_1(X0,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f126,f63])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f125,f62])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f124,f65])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK2(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK2(sK1)))
      | ~ l1_struct_0(sK1) ) ),
    inference(resolution,[],[f122,f64])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X0,sK1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f120,f58])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X0,sK1)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_waybel_0(sK1,X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f118,f59])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ r2_waybel_0(X0,X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f117,f57])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_struct_0(X5)
      | ~ r2_waybel_0(X2,X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ r2_hidden(X3,u1_struct_0(sK0))
      | v2_struct_0(X2)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_waybel_0(X2,X5)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ l1_orders_2(X7)
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ r2_waybel_0(X7,X6,u1_struct_0(sK1))
      | ~ l1_waybel_0(X6,X7)
      | v2_struct_0(X6)
      | ~ r2_hidden(X8,u1_struct_0(sK0))
      | v2_struct_0(X7)
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f105,f62])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_struct_0(X4)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ r2_waybel_0(X4,X3,u1_struct_0(sK1))
      | ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X3)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f104,f73])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f103,f59])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f100,f58])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f99,f60])).

fof(f60,plain,(
    ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f98,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK5(X0,X1,X2,X3))
                      & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK6(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK5(X0,X1,X2,X3))
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK6(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
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
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X3,u1_struct_0(X0))
      | ~ r2_hidden(X4,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f93,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | ~ r2_hidden(X3,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f90,f81])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f89,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f88,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f87,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f61,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.48  % (8950)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.48  % (8947)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (8954)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.49  % (8948)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.49  % (8949)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (8967)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.49  % (8952)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (8953)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (8959)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  % (8964)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (8946)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (8961)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (8948)Refutation not found, incomplete strategy% (8948)------------------------------
% 0.22/0.50  % (8948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8953)Refutation not found, incomplete strategy% (8953)------------------------------
% 0.22/0.50  % (8953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8951)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (8958)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.50  % (8968)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (8948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8948)Memory used [KB]: 10618
% 0.22/0.50  % (8948)Time elapsed: 0.094 s
% 0.22/0.50  % (8948)------------------------------
% 0.22/0.50  % (8948)------------------------------
% 0.22/0.50  % (8965)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.50  % (8966)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.50  % (8953)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8953)Memory used [KB]: 10490
% 0.22/0.50  % (8953)Time elapsed: 0.091 s
% 0.22/0.50  % (8953)------------------------------
% 0.22/0.50  % (8953)------------------------------
% 0.22/0.50  % (8957)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (8961)Refutation not found, incomplete strategy% (8961)------------------------------
% 0.22/0.51  % (8961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8945)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (8961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8961)Memory used [KB]: 1663
% 0.22/0.51  % (8961)Time elapsed: 0.103 s
% 0.22/0.51  % (8961)------------------------------
% 0.22/0.51  % (8961)------------------------------
% 0.22/0.51  % (8963)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (8952)Refutation not found, incomplete strategy% (8952)------------------------------
% 0.22/0.51  % (8952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8952)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8952)Memory used [KB]: 6140
% 0.22/0.51  % (8952)Time elapsed: 0.105 s
% 0.22/0.51  % (8952)------------------------------
% 0.22/0.51  % (8952)------------------------------
% 0.22/0.51  % (8955)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (8955)Refutation not found, incomplete strategy% (8955)------------------------------
% 0.22/0.51  % (8955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8955)Memory used [KB]: 10490
% 0.22/0.51  % (8955)Time elapsed: 0.002 s
% 0.22/0.51  % (8955)------------------------------
% 0.22/0.51  % (8955)------------------------------
% 0.22/0.52  % (8965)Refutation not found, incomplete strategy% (8965)------------------------------
% 0.22/0.52  % (8965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8965)Memory used [KB]: 6140
% 0.22/0.52  % (8965)Time elapsed: 0.108 s
% 0.22/0.52  % (8965)------------------------------
% 0.22/0.52  % (8965)------------------------------
% 0.22/0.52  % (8956)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (8960)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (8951)Refutation not found, incomplete strategy% (8951)------------------------------
% 0.22/0.52  % (8951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8951)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8951)Memory used [KB]: 10618
% 0.22/0.52  % (8951)Time elapsed: 0.080 s
% 0.22/0.52  % (8951)------------------------------
% 0.22/0.52  % (8951)------------------------------
% 0.22/0.52  % (8964)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f217,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    l1_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    (~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f42,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ? [X1] : (~r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f13])).
% 0.22/0.52  fof(f13,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    ~l1_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f216,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    l1_waybel_0(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f216,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f215,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | ~l1_orders_2(sK1)) )),
% 0.22/0.52    inference(resolution,[],[f214,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(sK1) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f213,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | ~l1_struct_0(sK1)) )),
% 0.22/0.52    inference(resolution,[],[f211,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (l1_waybel_0(sK2(X0),X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ! [X0] : ((v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0)) & l1_waybel_0(sK2(X0),X0)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)) => (v7_waybel_0(sK2(X0)) & v4_orders_2(sK2(X0)) & ~v2_struct_0(sK2(X0)) & l1_waybel_0(sK2(X0),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_waybel_0)).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_waybel_0(sK2(sK1),X0) | v2_struct_0(X0) | ~l1_struct_0(X0) | ~l1_waybel_0(sK1,X1) | ~l1_struct_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f210,f63])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_orders_2(sK1) | v2_struct_0(X0) | ~l1_waybel_0(sK2(sK1),X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f208,f62])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(sK1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(sK2(sK1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f203,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK2(sK1)) | ~l1_waybel_0(sK2(sK1),X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f202,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_4_waybel_9(X0,X1),u1_struct_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_4_waybel_9)).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f201,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f57])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f199,f59])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_waybel_0(sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f58])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~l1_waybel_0(sK1,X1) | v2_struct_0(sK1) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(resolution,[],[f193,f82])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f192,f56])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f191,f57])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f190])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f189,f64])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_waybel_0(sK2(sK0),X1) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f187,f57])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~l1_waybel_0(sK2(sK0),X1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f182,f65])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~l1_waybel_0(sK2(sK0),X2) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 0.22/0.53    inference(resolution,[],[f181,f82])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK2(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f57])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK0))) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK0))) | ~l1_struct_0(sK0) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f178,f64])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f177,f65])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | v2_struct_0(sK2(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f176,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0] : (v4_orders_2(sK2(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | ~v4_orders_2(sK2(X0)) | v2_struct_0(sK2(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f175,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (v7_waybel_0(sK2(X0)) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | ~v7_waybel_0(sK2(X0)) | ~v4_orders_2(sK2(X0)) | v2_struct_0(sK2(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f174,f56])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | ~v7_waybel_0(sK2(X0)) | ~v4_orders_2(sK2(X0)) | v2_struct_0(sK2(X0)) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f57])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | ~v7_waybel_0(sK2(X0)) | ~v4_orders_2(sK2(X0)) | v2_struct_0(sK2(X0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f172])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK2(X0),sK0) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X0))) | ~l1_struct_0(X0) | ~l1_waybel_0(sK2(X0),sK0) | ~v7_waybel_0(sK2(X0)) | ~v4_orders_2(sK2(X0)) | v2_struct_0(sK2(X0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f171,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0)) | ~l1_waybel_0(sK2(X1),sK0) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(sK2(X1))) | ~l1_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f66])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK2(X1),sK0) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK2(X1))) | ~v4_orders_2(sK2(X1)) | ~l1_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f65])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK2(X1),sK0) | v2_struct_0(sK2(X1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,sK2(X1),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK2(X1))) | ~v4_orders_2(sK2(X1)) | ~l1_struct_0(X1)) )),
% 0.22/0.53    inference(resolution,[],[f167,f67])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X6,X8,X7,X5] : (~v7_waybel_0(X6) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~l1_waybel_0(X6,sK0) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~v4_orders_2(X6)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f56])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~l1_waybel_0(X6,sK0) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,X6,u1_struct_0(sK0)) | ~v7_waybel_0(X6) | ~v4_orders_2(X6) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f163,f57])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~l1_waybel_0(X6,sK0) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,X6,u1_struct_0(sK0)) | ~v7_waybel_0(X6) | ~v4_orders_2(X6) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f162])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~l1_waybel_0(X6,sK0) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK0,X6,u1_struct_0(sK0)) | ~l1_waybel_0(X6,sK0) | ~v7_waybel_0(X6) | ~v4_orders_2(X6) | v2_struct_0(X6) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f160,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow_6)).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_waybel_0(sK0,X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f158,f56])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~r2_waybel_0(sK0,X2,u1_struct_0(sK0)) | ~l1_waybel_0(X2,sK0) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(sK2(sK1))) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f149,f57])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~l1_struct_0(X4) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~r2_waybel_0(X4,X3,u1_struct_0(sK0)) | ~l1_waybel_0(X3,X4) | v2_struct_0(X3) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(resolution,[],[f148,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(rectify,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f147,f57])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f146,f59])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK1,X3) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~l1_struct_0(X3)) )),
% 0.22/0.53    inference(resolution,[],[f145,f63])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(sK1) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(resolution,[],[f144,f62])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f143,f65])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | v2_struct_0(sK2(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f66])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f141,f67])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f64])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK2(sK1),sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f58])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK2(sK1),sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | v2_struct_0(sK1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK2(sK1),sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f137,f68])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r2_hidden(X4,u1_struct_0(sK0)) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f136,f65])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f135,f66])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f134,f67])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f64])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~l1_waybel_0(sK2(sK1),sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f131,f58])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X6,u1_struct_0(sK2(sK1))) | ~r1_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~l1_waybel_0(sK2(sK1),sK1) | ~v7_waybel_0(sK2(sK1)) | ~v4_orders_2(sK2(sK1)) | v2_struct_0(sK2(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f129,f69])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f128,f57])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~l1_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f127,f59])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(sK1,X3) | ~m1_subset_1(X0,u1_struct_0(sK2(sK1))) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~l1_struct_0(X3)) )),
% 0.22/0.53    inference(resolution,[],[f126,f63])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(sK1) | ~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2(sK1))) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(resolution,[],[f125,f62])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f124,f65])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK2(sK1)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,sK2(sK1),u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK2(sK1))) | ~l1_struct_0(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f122,f64])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X0,sK1) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,X0,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f120,f58])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~l1_waybel_0(X0,sK1) | v2_struct_0(X0) | ~r2_hidden(X1,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_waybel_0(sK1,X0,u1_struct_0(sK1)) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(resolution,[],[f118,f59])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~l1_waybel_0(X0,sK0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~r2_hidden(X2,u1_struct_0(sK0)) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~r2_waybel_0(X0,X1,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(X1))) )),
% 0.22/0.53    inference(resolution,[],[f117,f57])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_struct_0(X5) | ~r2_waybel_0(X2,X1,u1_struct_0(sK1)) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~r2_hidden(X3,u1_struct_0(sK0)) | v2_struct_0(X2) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~l1_waybel_0(X2,X5) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.53    inference(resolution,[],[f108,f63])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X6,X4,X8,X7,X5] : (~l1_orders_2(X7) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~r2_waybel_0(X7,X6,u1_struct_0(sK1)) | ~l1_waybel_0(X6,X7) | v2_struct_0(X6) | ~r2_hidden(X8,u1_struct_0(sK0)) | v2_struct_0(X7) | ~m1_subset_1(X4,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(resolution,[],[f105,f62])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~l1_struct_0(X4) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~r2_waybel_0(X4,X3,u1_struct_0(sK1)) | ~l1_waybel_0(X3,X4) | v2_struct_0(X3) | ~r2_hidden(X0,u1_struct_0(sK0)) | v2_struct_0(X4)) )),
% 0.22/0.53    inference(resolution,[],[f104,f73])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f103,f59])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f102,f56])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f101,f57])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f100,f58])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.22/0.53    inference(resolution,[],[f99,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | ~r2_hidden(X4,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f98,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK5(X0,X1,X2,X3)) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK6(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f52,f54,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK5(X0,X1,X2,X3)) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK6(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(rectify,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f96,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2) | r1_waybel_0(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k2_waybel_0(X0,X1,X2),k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r2_hidden(X3,u1_struct_0(X0)) | ~r2_hidden(X4,u1_struct_0(X1))) )),
% 0.22/0.53    inference(resolution,[],[f93,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v1_xboole_0(u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | v2_struct_0(X2) | ~r2_hidden(X3,u1_struct_0(X2))) )),
% 0.22/0.53    inference(resolution,[],[f90,f81])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f88,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f87,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(superposition,[],[f61,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_waybel_0)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (8964)------------------------------
% 0.22/0.53  % (8964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8964)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (8964)Memory used [KB]: 6268
% 0.22/0.53  % (8964)Time elapsed: 0.123 s
% 0.22/0.53  % (8964)------------------------------
% 0.22/0.53  % (8964)------------------------------
% 0.22/0.53  % (8962)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (8944)Success in time 0.172 s
%------------------------------------------------------------------------------

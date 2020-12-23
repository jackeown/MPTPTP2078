%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 360 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   23
%              Number of atoms          :  414 (1700 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f192,f257,f394])).

fof(f394,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f392,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

fof(f392,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f391,f181])).

fof(f181,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f178,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f93,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f34,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f391,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f390,f93])).

fof(f390,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f389,f65])).

fof(f65,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f32,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( ~ v10_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f54,f34])).

fof(f54,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f389,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f388,f31])).

fof(f388,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f379,f295])).

fof(f295,plain,
    ( ~ sQ2_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k5_lattices(sK0),sK1))
    | spl3_3 ),
    inference(resolution,[],[f265,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sQ2_eqProxy(X0,X1)
      | sQ2_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f265,plain,
    ( ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f264,f29])).

fof(f264,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f263,f181])).

fof(f263,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f262,f34])).

fof(f262,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f261,f69])).

fof(f69,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f68,f32])).

fof(f68,plain,
    ( ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f56,f34])).

fof(f56,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f261,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f260,f67])).

fof(f67,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f66,plain,
    ( ~ v10_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f55,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f260,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f259,f31])).

fof(f259,plain,
    ( v2_struct_0(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))
    | spl3_3 ),
    inference(resolution,[],[f256,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ sQ2_eqProxy(k2_lattices(X0,X1,X2),X1)
      | r1_lattices(X0,X1,X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f46])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f256,plain,
    ( ~ r1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl3_3
  <=> r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f379,plain,
    ( sQ2_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k5_lattices(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f252,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sQ2_eqProxy(k4_lattices(X0,X1,X2),k2_lattices(X0,X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
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
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f252,plain,(
    ! [X1] :
      ( ~ sQ2_eqProxy(k4_lattices(sK0,k5_lattices(sK0),sK1),X1)
      | sQ2_eqProxy(k5_lattices(sK0),X1) ) ),
    inference(resolution,[],[f136,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ2_eqProxy(X0,X1)
      | ~ sQ2_eqProxy(X1,X2)
      | sQ2_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f46])).

fof(f136,plain,(
    sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f135,f34])).

fof(f135,plain,
    ( ~ l3_lattices(sK0)
    | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f134,f33])).

fof(f33,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f133,f32])).

fof(f133,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(resolution,[],[f29,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sQ2_eqProxy(k5_lattices(X0),k4_lattices(X0,k5_lattices(X0),X1)) ) ),
    inference(equality_proxy_replacement,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

fof(f257,plain,
    ( ~ spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f165,f183,f254])).

fof(f183,plain,
    ( spl3_1
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

% (30770)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f165,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f164,f29])).

fof(f164,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f163,f34])).

fof(f163,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f162,f69])).

fof(f162,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f161,f67])).

fof(f161,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f160,f65])).

fof(f160,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(subsumption_resolution,[],[f159,f31])).

fof(f159,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f30,plain,(
    ~ r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f192,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f189,f93])).

fof(f189,plain,
    ( ~ l1_lattices(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_2
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f190,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f187,f183])).

fof(f57,plain,
    ( ~ l1_lattices(sK0)
    | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f31,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (30763)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (30776)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (30777)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (30775)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (30763)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (30758)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (30761)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (30759)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (30761)Refutation not found, incomplete strategy% (30761)------------------------------
% 0.21/0.51  % (30761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30760)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (30764)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (30767)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (30764)Refutation not found, incomplete strategy% (30764)------------------------------
% 0.21/0.51  % (30764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30778)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (30766)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (30761)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30761)Memory used [KB]: 10618
% 0.21/0.52  % (30761)Time elapsed: 0.092 s
% 0.21/0.52  % (30761)------------------------------
% 0.21/0.52  % (30761)------------------------------
% 0.21/0.52  % (30762)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (30768)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (30764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30764)Memory used [KB]: 10618
% 0.21/0.52  % (30764)Time elapsed: 0.104 s
% 0.21/0.52  % (30764)------------------------------
% 0.21/0.52  % (30764)------------------------------
% 0.21/0.52  % (30780)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (30765)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (30766)Refutation not found, incomplete strategy% (30766)------------------------------
% 0.21/0.52  % (30766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30766)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30765)Refutation not found, incomplete strategy% (30765)------------------------------
% 0.21/0.52  % (30765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30766)Memory used [KB]: 10618
% 0.21/0.52  % (30765)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30765)Memory used [KB]: 6140
% 0.21/0.52  % (30765)Time elapsed: 0.099 s
% 0.21/0.52  % (30765)------------------------------
% 0.21/0.52  % (30765)------------------------------
% 0.21/0.52  % (30766)Time elapsed: 0.105 s
% 0.21/0.52  % (30766)------------------------------
% 0.21/0.52  % (30766)------------------------------
% 0.21/0.52  % (30768)Refutation not found, incomplete strategy% (30768)------------------------------
% 0.21/0.52  % (30768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30768)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30768)Memory used [KB]: 10618
% 0.21/0.52  % (30768)Time elapsed: 0.115 s
% 0.21/0.52  % (30768)------------------------------
% 0.21/0.52  % (30768)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f190,f192,f257,f394])).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f393])).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    $false | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f392,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (~r3_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r3_lattices(X0,k5_lattices(X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).
% 0.21/0.52  fof(f392,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f391,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    v2_struct_0(sK0) | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f93,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~l1_lattices(X0) | m1_subset_1(k5_lattices(X0),u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    l1_lattices(sK0)),
% 0.21/0.52    inference(resolution,[],[f34,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    l3_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f390,f93])).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f389,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v6_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f64,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v10_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~v10_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f34])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.52    inference(resolution,[],[f31,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v6_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.52  fof(f389,plain,(
% 0.21/0.52    ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f388,f31])).
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f379,f295])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ~sQ2_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k5_lattices(sK0),sK1)) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f265,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sQ2_eqProxy(X0,X1) | sQ2_eqProxy(X1,X0)) )),
% 0.21/0.52    inference(equality_proxy_axiom,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f264,f29])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f263,f181])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f262,f34])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f261,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    v9_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f32])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~v10_lattices(sK0) | v9_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f34])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v9_lattices(sK0)),
% 0.21/0.52    inference(resolution,[],[f31,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v9_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f260,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    v8_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f32])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~v10_lattices(sK0) | v8_lattices(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f34])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v8_lattices(sK0)),
% 0.21/0.52    inference(resolution,[],[f31,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v8_lattices(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f259,f31])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~sQ2_eqProxy(k2_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f256,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~sQ2_eqProxy(k2_lattices(X0,X1,X2),X1) | r1_lattices(X0,X1,X2)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f40,f46])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ~r1_lattices(sK0,k5_lattices(sK0),sK1) | spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f254])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    spl3_3 <=> r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    sQ2_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k5_lattices(sK0),sK1)) | v2_struct_0(sK0) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f252,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | sQ2_eqProxy(k4_lattices(X0,X1,X2),k2_lattices(X0,X1,X2))) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f45,f46])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X1] : (~sQ2_eqProxy(k4_lattices(sK0,k5_lattices(sK0),sK1),X1) | sQ2_eqProxy(k5_lattices(sK0),X1)) )),
% 0.21/0.52    inference(resolution,[],[f136,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sQ2_eqProxy(X0,X1) | ~sQ2_eqProxy(X1,X2) | sQ2_eqProxy(X0,X2)) )),
% 0.21/0.52    inference(equality_proxy_axiom,[],[f46])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f135,f34])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f134,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v13_lattices(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~v13_lattices(sK0) | ~l3_lattices(sK0) | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f133,f32])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f31])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.52    inference(resolution,[],[f29,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | sQ2_eqProxy(k5_lattices(X0),k4_lattices(X0,k5_lattices(X0),X1))) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f39,f46])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    ~spl3_3 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f165,f183,f254])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl3_1 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  % (30770)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f29])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f34])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f162,f69])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f67])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f65])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f31])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(resolution,[],[f30,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ~r3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    $false | spl3_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f189,f93])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~l1_lattices(sK0) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f187])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl3_2 <=> l1_lattices(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f57,f187,f183])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~l1_lattices(sK0) | m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.52    inference(resolution,[],[f31,f42])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30763)------------------------------
% 0.21/0.52  % (30763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30763)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30763)Memory used [KB]: 6268
% 0.21/0.52  % (30763)Time elapsed: 0.099 s
% 0.21/0.52  % (30763)------------------------------
% 0.21/0.52  % (30763)------------------------------
% 0.21/0.52  % (30769)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (30757)Success in time 0.164 s
%------------------------------------------------------------------------------

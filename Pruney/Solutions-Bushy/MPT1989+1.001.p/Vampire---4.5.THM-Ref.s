%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1989+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:01 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 415 expanded)
%              Number of leaves         :   11 ( 139 expanded)
%              Depth                    :   21
%              Number of atoms          :  469 (3401 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f36])).

fof(f36,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK0)
        & v5_waybel_6(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_waybel_7(sK1,sK0)
      & v5_waybel_6(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f136,plain,(
    ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f135,f37])).

fof(f37,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f134,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f39,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f40,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f132,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f131,f41])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f44,plain,(
    ~ v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f130,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f129,f104])).

fof(f104,plain,(
    ~ v1_xboole_0(k5_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f36,f41,f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f40,f41,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f129,plain,
    ( v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f128,f105])).

fof(f105,plain,(
    v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f99,f36,f41,f42,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f128,plain,
    ( ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f127,f103])).

fof(f103,plain,(
    v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f99,f37,f41,f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f127,plain,
    ( ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f126,f102])).

fof(f102,plain,(
    v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f37,f38,f39,f40,f41,f43,f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f43,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f126,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f125,f106])).

fof(f106,plain,(
    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f41,f42,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f125,plain,
    ( ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f124,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | v4_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(superposition,[],[f60,f101])).

fof(f101,plain,(
    sK1 = k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f36,f37,f38,f41,f42,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK2(X0,X1)) = X1
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK2(X0,X1),X0)
                & v12_waybel_0(sK2(X0,X1),X0)
                & v1_waybel_0(sK2(X0,X1),X0)
                & ~ v1_xboole_0(sK2(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK2(X0,X1)) = X1
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK2(X0,X1),X0)
        & v12_waybel_0(sK2(X0,X1),X0)
        & v1_waybel_0(sK2(X0,X1),X0)
        & ~ v1_xboole_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).

%------------------------------------------------------------------------------

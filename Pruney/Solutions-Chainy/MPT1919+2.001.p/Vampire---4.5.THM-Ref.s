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
% DateTime   : Thu Dec  3 13:22:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 166 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 ( 501 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f96,f118])).

fof(f118,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f116,f24])).

fof(f24,plain,(
    ~ m1_yellow_6(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m1_yellow_6(X1,X0,X1)
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => m1_yellow_6(X1,X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => m1_yellow_6(X1,X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_6)).

fof(f116,plain,
    ( m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f115,f25])).

fof(f25,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f115,plain,
    ( ~ l1_struct_0(sK0)
    | m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f114,f66])).

fof(f66,plain,(
    m1_yellow_0(sK1,sK1) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    l1_orders_2(sK1) ),
    inference(resolution,[],[f48,f23])).

fof(f23,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | l1_orders_2(X0) ) ),
    inference(resolution,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_yellow_0(X0,X0) ) ),
    inference(subsumption_resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
      | m1_yellow_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_yellow_0(X0,X0) ) ),
    inference(resolution,[],[f28,f44])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f114,plain,
    ( ~ m1_yellow_0(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f113,f23])).

fof(f113,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( u1_waybel_0(sK0,sK1) != u1_waybel_0(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( u1_waybel_0(sK0,sK1) != u1_waybel_0(sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK1)
    | ~ l1_struct_0(sK0)
    | m1_yellow_6(sK1,sK0,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f32,f103])).

fof(f103,plain,
    ( u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f101,f51])).

fof(f51,plain,(
    v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f50,f23])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | v1_funct_1(u1_waybel_0(sK0,X0)) ) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v1_funct_1(u1_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f101,plain,
    ( ! [X0] :
        ( u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)
        | ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v1_funct_1(u1_waybel_0(sK0,sK1)) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f100,f59])).

fof(f59,plain,(
    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f58,f23])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( ! [X0] :
        ( u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)
        | ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(u1_waybel_0(sK0,sK1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)
        | ~ r1_tarski(u1_struct_0(sK1),X0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_waybel_0(sK0,sK1))
      | u1_waybel_0(sK0,sK1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f43,f59])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f87,plain,
    ( ! [X0] :
        ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1))
        | ~ r1_tarski(u1_struct_0(sK1),X0) )
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_1
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | ~ m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0)
      | m1_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f96,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f94,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f93,f23])).

fof(f93,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl2_2 ),
    inference(resolution,[],[f91,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_2
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ r1_tarski(u1_struct_0(sK1),X0)
      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f81,f59])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(u1_waybel_0(sK0,sK1),X0,X1)
      | ~ r1_tarski(X0,X2)
      | r2_relset_1(X0,X1,k2_partfun1(X0,X1,u1_waybel_0(sK0,sK1),X2),u1_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f39,f51])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X0,X2)
      | r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (7212)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (7222)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (7231)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (7231)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (7225)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (7208)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (7214)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (7211)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (7209)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (7230)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (7218)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (7216)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (7228)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (7217)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f92,f96,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~spl2_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    $false | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f116,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ~m1_yellow_6(sK1,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~m1_yellow_6(X1,X0,X1) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => m1_yellow_6(X1,X0,X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => m1_yellow_6(X1,X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_6)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f114,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    m1_yellow_0(sK1,sK1)),
% 0.20/0.51    inference(resolution,[],[f65,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    l1_orders_2(sK1)),
% 0.20/0.51    inference(resolution,[],[f48,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    l1_waybel_0(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | l1_orders_2(X0)) )),
% 0.20/0.51    inference(resolution,[],[f29,f25])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | l1_orders_2(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | m1_yellow_0(X0,X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f64,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) | m1_yellow_0(X0,X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_yellow_0(X0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f28,f44])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_yellow_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~m1_yellow_0(sK1,sK1) | ~l1_struct_0(sK0) | m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f23])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ~l1_waybel_0(sK1,sK0) | ~m1_yellow_0(sK1,sK1) | ~l1_struct_0(sK0) | m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    u1_waybel_0(sK0,sK1) != u1_waybel_0(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_yellow_0(sK1,sK1) | ~l1_struct_0(sK0) | m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    u1_waybel_0(sK0,sK1) != u1_waybel_0(sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_yellow_0(sK1,sK1) | ~l1_struct_0(sK0) | m1_yellow_6(sK1,sK0,sK1) | ~spl2_1),
% 0.20/0.51    inference(superposition,[],[f32,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(sK1)) | ~spl2_1),
% 0.20/0.51    inference(resolution,[],[f102,f44])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(sK1),X0) | u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0)) ) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v1_funct_1(u1_waybel_0(sK0,sK1))),
% 0.20/0.51    inference(resolution,[],[f50,f23])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | v1_funct_1(u1_waybel_0(sK0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f33,f25])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v1_funct_1(u1_waybel_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X0] : (u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) | ~r1_tarski(u1_struct_0(sK1),X0) | ~v1_funct_1(u1_waybel_0(sK0,sK1))) ) | ~spl2_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f100,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.51    inference(resolution,[],[f58,f23])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_waybel_0(X0,sK0) | m1_subset_1(u1_waybel_0(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))) )),
% 0.20/0.51    inference(resolution,[],[f35,f25])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X0] : (u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) | ~r1_tarski(u1_struct_0(sK1),X0) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(u1_waybel_0(sK0,sK1))) ) | ~spl2_1),
% 0.20/0.51    inference(resolution,[],[f97,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_waybel_0(sK0,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0) | ~r1_tarski(u1_struct_0(sK1),X0)) ) | ~spl2_1),
% 0.20/0.51    inference(resolution,[],[f87,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_waybel_0(sK0,sK1)) | u1_waybel_0(sK0,sK1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) )),
% 0.20/0.51    inference(resolution,[],[f43,f59])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0] : (r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1)) | ~r1_tarski(u1_struct_0(sK1),X0)) ) | ~spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl2_1 <=> ! [X0] : (~r1_tarski(u1_struct_0(sK1),X0) | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~l1_waybel_0(X1,X0) | ~l1_waybel_0(X2,X0) | ~m1_yellow_0(X2,X1) | ~l1_struct_0(X0) | m1_yellow_6(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl2_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    $false | spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f25])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~l1_struct_0(sK0) | spl2_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f23])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | spl2_2),
% 0.20/0.51    inference(resolution,[],[f91,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl2_2 <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f84,f89,f86])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~r1_tarski(u1_struct_0(sK1),X0) | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),X0),u1_waybel_0(sK0,sK1))) )),
% 0.20/0.51    inference(resolution,[],[f81,f59])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(u1_waybel_0(sK0,sK1),X0,X1) | ~r1_tarski(X0,X2) | r2_relset_1(X0,X1,k2_partfun1(X0,X1,u1_waybel_0(sK0,sK1),X2),u1_waybel_0(sK0,sK1))) )),
% 0.20/0.51    inference(resolution,[],[f39,f51])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X0,X2) | r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7231)------------------------------
% 0.20/0.51  % (7231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7231)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7231)Memory used [KB]: 10746
% 0.20/0.51  % (7231)Time elapsed: 0.097 s
% 0.20/0.51  % (7231)------------------------------
% 0.20/0.51  % (7231)------------------------------
% 0.20/0.51  % (7221)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (7204)Success in time 0.158 s
%------------------------------------------------------------------------------

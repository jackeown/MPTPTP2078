%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 (1548 expanded)
%              Number of leaves         :   26 ( 568 expanded)
%              Depth                    :   28
%              Number of atoms          :  765 (10129 expanded)
%              Number of equality atoms :   95 ( 287 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f175,f199,f215,f227])).

fof(f227,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f225,f58])).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
      | ~ v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                  | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1)
                | ~ v2_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1)
              | ~ v2_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1)
            | ~ v2_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1)
          | ~ v2_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
        | ~ v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                | ~ v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ( m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                  & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ( m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)
                & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_9)).

fof(f225,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f224,f60])).

fof(f60,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f224,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f223,f109])).

fof(f109,plain,
    ( ~ v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_1
  <=> v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f223,plain,
    ( v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f222,f206])).

fof(f206,plain,
    ( v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f205,f188])).

fof(f188,plain,(
    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f187,f176])).

fof(f176,plain,(
    m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))) ),
    inference(resolution,[],[f163,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f163,plain,(
    l1_orders_2(k4_waybel_9(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f162,f58])).

fof(f162,plain,
    ( l1_orders_2(k4_waybel_9(sK0,sK1,sK2))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f143,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f143,plain,(
    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f142,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f142,plain,
    ( l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f58])).

fof(f141,plain,
    ( l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f126,f60])).

fof(f126,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | l1_waybel_0(k4_waybel_9(X0,sK1,sK2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f125,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    ! [X0] :
      ( l1_waybel_0(k4_waybel_9(X0,sK1,sK2),X0)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f187,plain,
    ( u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))) ),
    inference(subsumption_resolution,[],[f186,f177])).

fof(f177,plain,(
    ! [X0] : m1_subset_1(k2_wellord1(u1_orders_2(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(superposition,[],[f121,f122])).

fof(f122,plain,(
    ! [X2] : k2_wellord1(u1_orders_2(sK1),X2) = k1_toler_1(u1_orders_2(sK1),X2) ),
    inference(resolution,[],[f119,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

fof(f119,plain,(
    v1_relat_1(u1_orders_2(sK1)) ),
    inference(resolution,[],[f117,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f117,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f64,f116])).

fof(f116,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f115,f58])).

fof(f115,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f70,f60])).

fof(f121,plain,(
    ! [X1] : m1_subset_1(k1_toler_1(u1_orders_2(sK1),X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(resolution,[],[f119,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_toler_1)).

fof(f186,plain,
    ( u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | ~ m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))) ),
    inference(resolution,[],[f155,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f155,plain,(
    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ),
    inference(forward_demodulation,[],[f154,f122])).

fof(f154,plain,(
    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f153,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f58])).

fof(f152,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f59])).

fof(f151,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f60])).

fof(f150,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f61])).

fof(f149,plain,
    ( r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f143])).

fof(f147,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f140,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_orders_2(k4_waybel_9(X0,X1,X2)),k1_toler_1(u1_orders_2(X1),u1_struct_0(k4_waybel_9(X0,X1,X2))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

% (5312)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ( ( ! [X5] :
                              ( ~ r1_orders_2(X1,X2,X5)
                              | sK3(X1,X2,X3) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                          | ~ r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) )
                        & ( ( r1_orders_2(X1,X2,sK4(X1,X2,X3))
                            & sK3(X1,X2,X3) = sK4(X1,X2,X3)
                            & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
                          | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ( r1_orders_2(X1,X2,sK5(X1,X2,X7))
                                & sK5(X1,X2,X7) = X7
                                & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X2,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X3)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X2,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X3)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X2,X5)
              | sK3(X1,X2,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X2,X6)
              & sK3(X1,X2,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X2,X1] :
      ( ? [X6] :
          ( r1_orders_2(X1,X2,X6)
          & sK3(X1,X2,X3) = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK4(X1,X2,X3))
        & sK3(X1,X2,X3) = sK4(X1,X2,X3)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X7,X2,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X2,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X2,sK5(X1,X2,X7))
        & sK5(X1,X2,X7) = X7
        & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X6] :
                                ( r1_orders_2(X1,X2,X6)
                                & X4 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X7] :
                            ( ( r2_hidden(X7,u1_struct_0(X3))
                              | ! [X8] :
                                  ( ~ r1_orders_2(X1,X2,X8)
                                  | X7 != X8
                                  | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
                            & ( ? [X9] :
                                  ( r1_orders_2(X1,X2,X9)
                                  & X7 = X9
                                  & m1_subset_1(X9,u1_struct_0(X1)) )
                              | ~ r2_hidden(X7,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ? [X4] :
                          ( ( ! [X5] :
                                ( ~ r1_orders_2(X1,X2,X5)
                                | X4 != X5
                                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                            | ~ r2_hidden(X4,u1_struct_0(X3)) )
                          & ( ? [X5] :
                                ( r1_orders_2(X1,X2,X5)
                                & X4 = X5
                                & m1_subset_1(X5,u1_struct_0(X1)) )
                            | r2_hidden(X4,u1_struct_0(X3)) ) ) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & ! [X4] :
                            ( ( r2_hidden(X4,u1_struct_0(X3))
                              | ! [X5] :
                                  ( ~ r1_orders_2(X1,X2,X5)
                                  | X4 != X5
                                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                            & ( ? [X5] :
                                  ( r1_orders_2(X1,X2,X5)
                                  & X4 = X5
                                  & m1_subset_1(X5,u1_struct_0(X1)) )
                              | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f140,plain,(
    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f139,f57])).

fof(f139,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f124,f60])).

fof(f124,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | v6_waybel_0(k4_waybel_9(X0,sK1,sK2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f59])).

fof(f123,plain,(
    ! [X0] :
      ( v6_waybel_0(k4_waybel_9(X0,sK1,sK2),X0)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f92,f61])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f205,plain,
    ( u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f204,f122])).

fof(f204,plain,
    ( u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f201,f116])).

fof(f201,plain,
    ( u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f170,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

% (5308)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

fof(f170,plain,
    ( m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_3
  <=> m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f222,plain,
    ( ~ v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f220,f170])).

fof(f220,plain,
    ( ~ m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f218,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ m1_yellow_0(X2,X1)
      | ~ v4_yellow_0(X2,X1)
      | v2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

fof(f218,plain,
    ( m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f217,f58])).

fof(f217,plain,
    ( m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f216,f60])).

fof(f216,plain,
    ( m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f210,f161])).

fof(f161,plain,(
    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f160,f57])).

fof(f160,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f159,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f59])).

fof(f158,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f157,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f61])).

fof(f156,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f143])).

fof(f148,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f140,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f210,plain,
    ( m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f200,f143])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),X0)
        | m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),X0,sK1)
        | u1_waybel_0(X0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | ~ l1_waybel_0(sK1,X0)
        | ~ l1_struct_0(X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f170,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X2,X1)
      | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
      | m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(f215,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f213,f58])).

fof(f213,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f212,f60])).

fof(f212,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f211,f161])).

fof(f211,plain,
    ( u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f210,f113])).

fof(f113,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_2
  <=> m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f199,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f197,f174])).

fof(f174,plain,
    ( ~ r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_4
  <=> r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f197,plain,(
    r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) ),
    inference(superposition,[],[f189,f188])).

fof(f189,plain,(
    ! [X0] : r1_tarski(k2_wellord1(u1_orders_2(sK1),X0),u1_orders_2(sK1)) ),
    inference(superposition,[],[f88,f120])).

fof(f120,plain,(
    ! [X0] : k2_wellord1(u1_orders_2(sK1),X0) = k3_xboole_0(u1_orders_2(sK1),k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f175,plain,
    ( spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f166,f172,f168])).

fof(f166,plain,
    ( ~ r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))
    | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f165,f116])).

fof(f165,plain,
    ( ~ r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))
    | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f164,f163])).

fof(f164,plain,
    ( ~ r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))
    | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)
    | ~ l1_orders_2(k4_waybel_9(sK0,sK1,sK2))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f146,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

% (5297)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f146,plain,(
    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f57])).

fof(f145,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f58])).

fof(f144,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f128,f60])).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | r1_tarski(u1_struct_0(k4_waybel_9(X0,sK1,sK2)),u1_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f59])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(X0,sK1,sK2)),u1_struct_0(sK1))
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f77,f61])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (5297)Refutation not found, incomplete strategy% (5297)------------------------------
% (5297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5297)Termination reason: Refutation not found, incomplete strategy

% (5297)Memory used [KB]: 10618
% (5297)Time elapsed: 0.086 s
% (5297)------------------------------
% (5297)------------------------------
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f114,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f111,f107])).

fof(f62,plain,
    ( ~ m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)
    | ~ v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (5291)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (5302)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (5299)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (5301)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (5298)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (5293)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (5314)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (5292)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5302)Refutation not found, incomplete strategy% (5302)------------------------------
% 0.20/0.51  % (5302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5302)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5302)Memory used [KB]: 10490
% 0.20/0.51  % (5302)Time elapsed: 0.003 s
% 0.20/0.51  % (5302)------------------------------
% 0.20/0.51  % (5302)------------------------------
% 0.20/0.51  % (5292)Refutation not found, incomplete strategy% (5292)------------------------------
% 0.20/0.51  % (5292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5292)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5292)Memory used [KB]: 10618
% 0.20/0.51  % (5292)Time elapsed: 0.095 s
% 0.20/0.51  % (5292)------------------------------
% 0.20/0.51  % (5292)------------------------------
% 0.20/0.51  % (5300)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (5294)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (5306)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (5313)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (5303)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (5309)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (5307)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (5305)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (5296)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (5295)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (5311)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (5301)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (5315)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f114,f175,f199,f215,f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    spl6_1 | ~spl6_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f226])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    $false | (spl6_1 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f225,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    l1_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    (((~m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f40,f39,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1) | ~v2_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1) | ~v2_yellow_6(k4_waybel_9(sK0,X1,X2),sK0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((~m1_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1) | ~v2_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ? [X2] : ((~m1_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1) | ~v2_yellow_6(k4_waybel_9(sK0,sK1,X2),sK0,sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) => ((~m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) | ~v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f16])).
% 0.20/0.53  fof(f16,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (m1_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1) & v2_yellow_6(k4_waybel_9(X0,X1,X2),X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_9)).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | (spl6_1 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f224,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    l1_waybel_0(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f224,plain,(
% 0.20/0.53    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | (spl6_1 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f223,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | spl6_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl6_1 <=> v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f222,f206])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f205,f188])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f187,f176])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))),
% 0.20/0.53    inference(resolution,[],[f163,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    l1_orders_2(k4_waybel_9(sK0,sK1,sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f162,f58])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    l1_orders_2(k4_waybel_9(sK0,sK1,sK2)) | ~l1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f143,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | l1_orders_2(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f142,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f141,f58])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f126,f60])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_waybel_0(sK1,X0) | l1_waybel_0(k4_waybel_9(X0,sK1,sK2),X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X0] : (l1_waybel_0(k4_waybel_9(X0,sK1,sK2),X0) | ~l1_waybel_0(sK1,X0) | v2_struct_0(sK1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f93,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f186,f177])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_wellord1(u1_orders_2(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.53    inference(superposition,[],[f121,f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ( ! [X2] : (k2_wellord1(u1_orders_2(sK1),X2) = k1_toler_1(u1_orders_2(sK1),X2)) )),
% 0.20/0.53    inference(resolution,[],[f119,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k1_toler_1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_wellord1(X0,X1) = k1_toler_1(X0,X1) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X0) => k2_wellord1(X0,X1) = k1_toler_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_toler_1)).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    v1_relat_1(u1_orders_2(sK1))),
% 0.20/0.53    inference(resolution,[],[f117,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))),
% 0.20/0.53    inference(resolution,[],[f64,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    l1_orders_2(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f115,f58])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    l1_orders_2(sK1) | ~l1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f70,f60])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X1] : (m1_subset_1(k1_toler_1(u1_orders_2(sK1),X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 0.20/0.53    inference(resolution,[],[f119,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X0) => m1_subset_1(k1_toler_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_toler_1)).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) = k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~m1_subset_1(k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))) | ~m1_subset_1(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))),
% 0.20/0.53    inference(resolution,[],[f155,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))),
% 0.20/0.53    inference(forward_demodulation,[],[f154,f122])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))),
% 0.20/0.53    inference(subsumption_resolution,[],[f153,f57])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f152,f58])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f151,f59])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f150,f60])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f149,f61])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f147,f143])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ~l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | r2_relset_1(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f140,f98])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | r2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_orders_2(k4_waybel_9(X0,X1,X2)),k1_toler_1(u1_orders_2(X1),u1_struct_0(k4_waybel_9(X0,X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | k4_waybel_9(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  % (5312)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ((! [X5] : (~r1_orders_2(X1,X2,X5) | sK3(X1,X2,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3))) & ((r1_orders_2(X1,X2,sK4(X1,X2,X3)) & sK3(X1,X2,X3) = sK4(X1,X2,X3) & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X3)) | ! [X8] : (~r1_orders_2(X1,X2,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & ((r1_orders_2(X1,X2,sK5(X1,X2,X7)) & sK5(X1,X2,X7) = X7 & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X3))))) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X3,X2,X1] : (? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X6] : (r1_orders_2(X1,X2,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3)))) => ((! [X5] : (~r1_orders_2(X1,X2,X5) | sK3(X1,X2,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3))) & (? [X6] : (r1_orders_2(X1,X2,X6) & sK3(X1,X2,X3) = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),u1_struct_0(X3)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X3,X2,X1] : (? [X6] : (r1_orders_2(X1,X2,X6) & sK3(X1,X2,X3) = X6 & m1_subset_1(X6,u1_struct_0(X1))) => (r1_orders_2(X1,X2,sK4(X1,X2,X3)) & sK3(X1,X2,X3) = sK4(X1,X2,X3) & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X7,X2,X1] : (? [X9] : (r1_orders_2(X1,X2,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) => (r1_orders_2(X1,X2,sK5(X1,X2,X7)) & sK5(X1,X2,X7) = X7 & m1_subset_1(sK5(X1,X2,X7),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X6] : (r1_orders_2(X1,X2,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X3)) | ! [X8] : (~r1_orders_2(X1,X2,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & (? [X9] : (r1_orders_2(X1,X2,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X3))))) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(rectify,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3)))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f57])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f58])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f124,f60])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_waybel_0(sK1,X0) | v6_waybel_0(k4_waybel_9(X0,sK1,sK2),X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f123,f59])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ( ! [X0] : (v6_waybel_0(k4_waybel_9(X0,sK1,sK2),X0) | ~l1_waybel_0(sK1,X0) | v2_struct_0(sK1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f92,f61])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k2_wellord1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~spl6_3),
% 0.20/0.53    inference(forward_demodulation,[],[f204,f122])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f201,f116])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    u1_orders_2(k4_waybel_9(sK0,sK1,sK2)) != k1_toler_1(u1_orders_2(sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~l1_orders_2(sK1) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f170,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) | v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  % (5308)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v4_yellow_0(X1,X0) | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))) & (u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) | ~v4_yellow_0(X1,X0))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v4_yellow_0(X1,X0) <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => (v4_yellow_0(X1,X0) <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~spl6_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f168])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    spl6_3 <=> m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.53  fof(f222,plain,(
% 0.20/0.53    ~v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f220,f170])).
% 0.20/0.53  fof(f220,plain,(
% 0.20/0.53    ~m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~v4_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f218,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1) | v2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1)) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | (~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1))) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f217,f58])).
% 0.20/0.53  fof(f217,plain,(
% 0.20/0.53    m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f216,f60])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f210,f161])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f160,f57])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f159,f58])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f158,f59])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f157,f60])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f61])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f148,f143])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ~l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f140,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | u1_waybel_0(X0,k4_waybel_9(X0,X1,X2)) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(k4_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f200,f143])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),X0) | m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),X0,sK1) | u1_waybel_0(X0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) ) | ~spl6_3),
% 0.20/0.53    inference(resolution,[],[f170,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_yellow_0(X2,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).
% 0.20/0.53  fof(f215,plain,(
% 0.20/0.53    spl6_2 | ~spl6_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f214])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    $false | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f213,f58])).
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    ~l1_struct_0(sK0) | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f212,f60])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f211,f161])).
% 0.20/0.53  fof(f211,plain,(
% 0.20/0.53    u1_waybel_0(sK0,k4_waybel_9(sK0,sK1,sK2)) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | (spl6_2 | ~spl6_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f210,f113])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ~m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | spl6_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl6_2 <=> m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    spl6_4),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    $false | spl6_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f197,f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    ~r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) | spl6_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f172])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    spl6_4 <=> r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1))),
% 0.20/0.53    inference(superposition,[],[f189,f188])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k2_wellord1(u1_orders_2(sK1),X0),u1_orders_2(sK1))) )),
% 0.20/0.53    inference(superposition,[],[f88,f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X0] : (k2_wellord1(u1_orders_2(sK1),X0) = k3_xboole_0(u1_orders_2(sK1),k2_zfmisc_1(X0,X0))) )),
% 0.20/0.53    inference(resolution,[],[f119,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    spl6_3 | ~spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f166,f172,f168])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    ~r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f165,f116])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    ~r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~l1_orders_2(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f164,f163])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ~r1_tarski(u1_orders_2(k4_waybel_9(sK0,sK1,sK2)),u1_orders_2(sK1)) | m1_yellow_0(k4_waybel_9(sK0,sK1,sK2),sK1) | ~l1_orders_2(k4_waybel_9(sK0,sK1,sK2)) | ~l1_orders_2(sK1)),
% 0.20/0.53    inference(resolution,[],[f146,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  % (5297)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f145,f57])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f144,f58])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f128,f60])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_waybel_0(sK1,X0) | r1_tarski(u1_struct_0(k4_waybel_9(X0,sK1,sK2)),u1_struct_0(sK1)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f127,f59])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,sK1,sK2)),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,X0) | v2_struct_0(sK1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f77,f61])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  % (5297)Refutation not found, incomplete strategy% (5297)------------------------------
% 0.20/0.53  % (5297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5297)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5297)Memory used [KB]: 10618
% 0.20/0.53  % (5297)Time elapsed: 0.086 s
% 0.20/0.53  % (5297)------------------------------
% 0.20/0.53  % (5297)------------------------------
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~spl6_1 | ~spl6_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f62,f111,f107])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ~m1_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1) | ~v2_yellow_6(k4_waybel_9(sK0,sK1,sK2),sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (5301)------------------------------
% 0.20/0.53  % (5301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5301)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (5301)Memory used [KB]: 10746
% 0.20/0.53  % (5301)Time elapsed: 0.119 s
% 0.20/0.53  % (5301)------------------------------
% 0.20/0.53  % (5301)------------------------------
% 0.20/0.54  % (5290)Success in time 0.18 s
%------------------------------------------------------------------------------

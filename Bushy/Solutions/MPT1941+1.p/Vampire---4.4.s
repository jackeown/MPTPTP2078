%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t39_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:55 EDT 2019

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 652 expanded)
%              Number of leaves         :   21 ( 208 expanded)
%              Depth                    :   20
%              Number of atoms          :  527 (4896 expanded)
%              Number of equality atoms :   50 ( 220 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12387,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f179,f180,f12273,f12299,f12386])).

fof(f12386,plain,
    ( ~ spl10_0
    | spl10_5 ),
    inference(avatar_contradiction_clause,[],[f12385])).

fof(f12385,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f12380,f97])).

fof(f97,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ( ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    & ( ( v3_pre_topc(sK2,sK0)
        & r2_hidden(sK1,sK2) )
      | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2)
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,sK0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & ( ( v3_pre_topc(X2,sK0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ v3_pre_topc(X2,X0)
              | ~ r2_hidden(sK1,X2)
              | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK1))) )
            & ( ( v3_pre_topc(X2,X0)
                & r2_hidden(sK1,X2) )
              | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v3_pre_topc(X2,X0)
            | ~ r2_hidden(X1,X2)
            | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & ( ( v3_pre_topc(X2,X0)
              & r2_hidden(X1,X2) )
            | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(sK2,X0)
          | ~ r2_hidden(X1,sK2)
          | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(X0,X1))) )
        & ( ( v3_pre_topc(sK2,X0)
            & r2_hidden(X1,sK2) )
          | r2_hidden(sK2,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(X2,X0)
                | ~ r2_hidden(X1,X2)
                | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & ( ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) )
                | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                <=> ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',t39_yellow_6)).

fof(f12380,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_5 ),
    inference(resolution,[],[f12303,f12294])).

fof(f12294,plain,
    ( r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f12293,f97])).

fof(f12293,plain,
    ( r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_0 ),
    inference(superposition,[],[f162,f11874])).

fof(f11874,plain,(
    ! [X1] :
      ( u1_struct_0(k9_yellow_6(sK0,X1)) = a_2_0_yellow_6(sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f11873,f8231])).

fof(f8231,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0 ),
    inference(subsumption_resolution,[],[f8226,f151])).

fof(f151,plain,(
    ! [X0] : m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f109,f103])).

fof(f103,plain,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k1_yellow_1(X0) = k1_wellord2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',redefinition_k1_yellow_1)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',dt_k1_yellow_1)).

fof(f8226,plain,(
    ! [X0] :
      ( u1_struct_0(g1_orders_2(X0,k1_wellord2(X0))) = X0
      | ~ m1_subset_1(k1_wellord2(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(equality_resolution,[],[f3605])).

fof(f3605,plain,(
    ! [X6,X8,X7] :
      ( g1_orders_2(X7,X8) != g1_orders_2(X6,k1_wellord2(X6))
      | u1_struct_0(g1_orders_2(X6,k1_wellord2(X6))) = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) ) ),
    inference(superposition,[],[f131,f434])).

fof(f434,plain,(
    ! [X1] : g1_orders_2(X1,k1_wellord2(X1)) = g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_wellord2(X1))),u1_orders_2(g1_orders_2(X1,k1_wellord2(X1)))) ),
    inference(subsumption_resolution,[],[f431,f156])).

fof(f156,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f111,f150])).

fof(f150,plain,(
    ! [X0] : g1_orders_2(X0,k1_wellord2(X0)) = k2_yellow_1(X0) ),
    inference(definition_unfolding,[],[f104,f103])).

fof(f104,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',d1_yellow_1)).

fof(f111,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',dt_k2_yellow_1)).

fof(f431,plain,(
    ! [X1] :
      ( g1_orders_2(X1,k1_wellord2(X1)) = g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_wellord2(X1))),u1_orders_2(g1_orders_2(X1,k1_wellord2(X1))))
      | ~ l1_orders_2(g1_orders_2(X1,k1_wellord2(X1))) ) ),
    inference(resolution,[],[f119,f157])).

fof(f157,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_wellord2(X0))) ),
    inference(definition_unfolding,[],[f110,f150])).

fof(f110,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',abstractness_v1_orders_2)).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',free_g1_orders_2)).

fof(f11873,plain,(
    ! [X1] :
      ( u1_struct_0(k9_yellow_6(sK0,X1)) = u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK0,X1),k1_wellord2(a_2_0_yellow_6(sK0,X1))))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f11870,f156])).

fof(f11870,plain,(
    ! [X1] :
      ( u1_struct_0(k9_yellow_6(sK0,X1)) = u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK0,X1),k1_wellord2(a_2_0_yellow_6(sK0,X1))))
      | ~ l1_orders_2(g1_orders_2(a_2_0_yellow_6(sK0,X1),k1_wellord2(a_2_0_yellow_6(sK0,X1))))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f115,f1644])).

fof(f1644,plain,(
    ! [X0] :
      ( k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_wellord2(a_2_0_yellow_6(sK0,X0))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1643,f94])).

fof(f94,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f1643,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_wellord2(a_2_0_yellow_6(sK0,X0))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1642,f96])).

fof(f96,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f1642,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_wellord2(a_2_0_yellow_6(sK0,X0))))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f158,f95])).

fof(f95,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k9_yellow_6(X0,X1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_wellord2(a_2_0_yellow_6(X0,X1))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f120,f150])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',d17_yellow_6)).

fof(f115,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',t12_yellow_6)).

fof(f162,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl10_0
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f12303,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f177,f11578])).

fof(f11578,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f11577,f94])).

fof(f11577,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11576,f95])).

fof(f11576,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11575,f96])).

fof(f11575,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f11574])).

fof(f11574,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1083,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( v3_pre_topc(sK6(X0,X1,X2),X1)
            & r2_hidden(X2,sK6(X0,X1,X2))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f85,f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_pre_topc(X4,X1)
          & r2_hidden(X2,X4)
          & X0 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v3_pre_topc(sK6(X0,X1,X2),X1)
        & r2_hidden(X2,sK6(X0,X1,X2))
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( v3_pre_topc(X4,X1)
              & r2_hidden(X2,X4)
              & X0 = X4
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( v3_pre_topc(X3,X1)
              & r2_hidden(X2,X3)
              & X0 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',fraenkel_a_2_0_yellow_6)).

fof(f1083,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK6(X0,sK0,X1),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1082,f94])).

fof(f1082,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK6(X0,sK0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1081,f96])).

fof(f1081,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(sK6(X0,sK0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f143,f95])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | v3_pre_topc(sK6(X0,X1,X2),X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f177,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl10_5
  <=> ~ v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f12299,plain,
    ( ~ spl10_0
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f12298])).

fof(f12298,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f12295,f171])).

fof(f171,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl10_3
  <=> ~ r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f12295,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_0 ),
    inference(resolution,[],[f12294,f12133])).

fof(f12133,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,a_2_0_yellow_6(sK0,sK1))
      | r2_hidden(sK1,X6) ) ),
    inference(resolution,[],[f11538,f97])).

fof(f11538,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f11537,f94])).

fof(f11537,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11536,f95])).

fof(f11536,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11525,f96])).

fof(f11525,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f11524])).

fof(f11524,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1044,f141])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK6(X0,sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1043,f94])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,sK6(X0,sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1042,f96])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X1,sK6(X0,sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f142,f95])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | r2_hidden(X2,sK6(X0,X1,X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f12273,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f12272])).

fof(f12272,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f12267,f168])).

fof(f168,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl10_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f12267,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f11693,f12266])).

fof(f12266,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f12255,f97])).

fof(f12255,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1 ),
    inference(superposition,[],[f165,f11874])).

fof(f165,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl10_1
  <=> ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f11693,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,a_2_0_yellow_6(sK0,X0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f11690,f98])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f75])).

fof(f11690,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,a_2_0_yellow_6(sK0,X0)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f2172,f174])).

fof(f174,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl10_4
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f2172,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2171,f94])).

fof(f2171,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2170,f96])).

fof(f2170,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2074,f95])).

fof(f2074,plain,(
    ! [X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | r2_hidden(X3,a_2_0_yellow_6(X1,X2))
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f159,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t39_yellow_6.p',t4_subset)).

fof(f159,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow_6(X1,X2))
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f180,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f99,f167,f161])).

fof(f99,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f179,plain,
    ( spl10_0
    | spl10_4 ),
    inference(avatar_split_clause,[],[f100,f173,f161])).

fof(f100,plain,
    ( v3_pre_topc(sK2,sK0)
    | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f178,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f101,f176,f170,f164])).

fof(f101,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------

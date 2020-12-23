%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t26_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:48 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 289 expanded)
%              Number of leaves         :   23 ( 118 expanded)
%              Depth                    :   13
%              Number of atoms          :  426 ( 912 expanded)
%              Number of equality atoms :    7 (  35 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f88,f108,f111,f121,f133,f152,f156,f187,f195,f252,f297,f360,f473,f569,f578,f590])).

fof(f590,plain,
    ( ~ spl9_0
    | ~ spl9_4
    | spl9_11
    | ~ spl9_136 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_11
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f588,f120])).

fof(f120,plain,
    ( ~ v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl9_11
  <=> ~ v12_waybel_0(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f588,plain,
    ( v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f587,f75])).

fof(f75,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl9_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f587,plain,
    ( ~ l1_orders_2(sK0)
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_4
    | ~ spl9_136 ),
    inference(subsumption_resolution,[],[f580,f87])).

fof(f87,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_4
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f580,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_136 ),
    inference(resolution,[],[f577,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',d19_waybel_0)).

fof(f577,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl9_136
  <=> r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f578,plain,
    ( spl9_136
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f573,f567,f576])).

fof(f567,plain,
    ( spl9_134
  <=> sP7(sK3(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f573,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl9_134 ),
    inference(resolution,[],[f568,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',d4_tarski)).

fof(f568,plain,
    ( sP7(sK3(sK0,k3_tarski(sK1)),sK1)
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f567])).

fof(f569,plain,
    ( spl9_134
    | ~ spl9_56
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f563,f471,f250,f567])).

fof(f250,plain,
    ( spl9_56
  <=> r2_hidden(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f471,plain,
    ( spl9_112
  <=> r2_hidden(sK3(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f563,plain,
    ( sP7(sK3(sK0,k3_tarski(sK1)),sK1)
    | ~ spl9_56
    | ~ spl9_112 ),
    inference(resolution,[],[f477,f251])).

fof(f251,plain,
    ( r2_hidden(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f250])).

fof(f477,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK8(sK1,sK2(sK0,k3_tarski(sK1))),X1)
        | sP7(sK3(sK0,k3_tarski(sK1)),X1) )
    | ~ spl9_112 ),
    inference(resolution,[],[f472,f64])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f472,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl9_112 ),
    inference(avatar_component_clause,[],[f471])).

fof(f473,plain,
    ( spl9_112
    | ~ spl9_0
    | ~ spl9_16
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_56
    | ~ spl9_68
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f466,f358,f295,f250,f185,f154,f131,f74,f471])).

fof(f131,plain,
    ( spl9_16
  <=> m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f154,plain,
    ( spl9_28
  <=> m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f185,plain,
    ( spl9_36
  <=> r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f295,plain,
    ( spl9_68
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f358,plain,
    ( spl9_84
  <=> m1_subset_1(sK8(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f466,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl9_0
    | ~ spl9_16
    | ~ spl9_28
    | ~ spl9_36
    | ~ spl9_56
    | ~ spl9_68
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f465,f155])).

fof(f155,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f154])).

fof(f465,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl9_0
    | ~ spl9_16
    | ~ spl9_36
    | ~ spl9_56
    | ~ spl9_68
    | ~ spl9_84 ),
    inference(resolution,[],[f464,f186])).

fof(f186,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f185])).

fof(f464,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK2(sK0,k3_tarski(sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK8(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl9_0
    | ~ spl9_16
    | ~ spl9_56
    | ~ spl9_68
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f462,f132])).

fof(f132,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f462,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2(sK0,k3_tarski(sK1)))
        | r2_hidden(X0,sK8(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl9_0
    | ~ spl9_56
    | ~ spl9_68
    | ~ spl9_84 ),
    inference(resolution,[],[f375,f296])).

fof(f296,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f295])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK8(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK8(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl9_0
    | ~ spl9_56
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f374,f373])).

fof(f373,plain,
    ( v12_waybel_0(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK0)
    | ~ spl9_56
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f366,f251])).

fof(f366,plain,
    ( ~ r2_hidden(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | v12_waybel_0(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK0)
    | ~ spl9_84 ),
    inference(resolution,[],[f359,f43])).

fof(f43,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v12_waybel_0(X2,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v12_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) )
          & ! [X2] :
              ( v12_waybel_0(X2,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X2,X1)
                   => v12_waybel_0(X2,X0) ) )
             => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v12_waybel_0(X2,X0) ) )
           => ( m1_subset_1(k5_setfam_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',t26_waybel_0)).

fof(f359,plain,
    ( m1_subset_1(sK8(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f358])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK8(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK8(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ v12_waybel_0(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK0) )
    | ~ spl9_0
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f370,f75])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK8(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK8(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ v12_waybel_0(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK0) )
    | ~ spl9_84 ),
    inference(resolution,[],[f359,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f360,plain,
    ( spl9_84
    | ~ spl9_2
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f356,f250,f78,f358])).

fof(f78,plain,
    ( spl9_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f356,plain,
    ( m1_subset_1(sK8(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2
    | ~ spl9_56 ),
    inference(resolution,[],[f276,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f276,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | m1_subset_1(sK8(sK1,sK2(sK0,k3_tarski(sK1))),X1) )
    | ~ spl9_56 ),
    inference(resolution,[],[f251,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',t4_subset)).

fof(f297,plain,
    ( spl9_68
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f200,f193,f295])).

fof(f193,plain,
    ( spl9_38
  <=> sP7(sK2(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f200,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK8(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl9_38 ),
    inference(resolution,[],[f194,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,sK8(X0,X2)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f194,plain,
    ( sP7(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f193])).

fof(f252,plain,
    ( spl9_56
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f201,f193,f250])).

fof(f201,plain,
    ( r2_hidden(sK8(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl9_38 ),
    inference(resolution,[],[f194,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(sK8(X0,X2),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f195,plain,
    ( spl9_38
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f158,f150,f193])).

fof(f150,plain,
    ( spl9_26
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f158,plain,
    ( sP7(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl9_26 ),
    inference(resolution,[],[f151,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | sP7(X2,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f151,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f150])).

fof(f187,plain,
    ( spl9_36
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f114,f106,f86,f78,f74,f185])).

fof(f106,plain,
    ( spl9_9
  <=> ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f114,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f99,f112])).

fof(f112,plain,
    ( ~ v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f107,f81])).

fof(f81,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl9_2 ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',redefinition_k5_setfam_1)).

fof(f107,plain,
    ( ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f99,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f93,f75])).

fof(f93,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( spl9_28
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f116,f106,f86,f78,f74,f154])).

fof(f116,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f97,f112])).

fof(f97,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f91,f75])).

fof(f91,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f87,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f152,plain,
    ( spl9_26
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f115,f106,f86,f78,f74,f150])).

fof(f115,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f98,f112])).

fof(f98,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f92,f75])).

fof(f92,plain,
    ( ~ l1_orders_2(sK0)
    | r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f87,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,
    ( spl9_16
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(avatar_split_clause,[],[f113,f106,f86,f78,f74,f131])).

fof(f113,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f101,f112])).

fof(f101,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_0
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f95,f75])).

fof(f95,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,
    ( ~ spl9_11
    | ~ spl9_2
    | spl9_9 ),
    inference(avatar_split_clause,[],[f112,f106,f78,f119])).

fof(f111,plain,
    ( ~ spl9_2
    | ~ spl9_4
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f109,f87])).

fof(f109,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f104,f81])).

fof(f104,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_7
  <=> ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f108,plain,
    ( ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f44,f106,f103])).

fof(f44,plain,
    ( ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,
    ( spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f84,f78,f86])).

fof(f84,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f82,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2 ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t26_waybel_0.p',dt_k5_setfam_1)).

fof(f80,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f46,f74])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------

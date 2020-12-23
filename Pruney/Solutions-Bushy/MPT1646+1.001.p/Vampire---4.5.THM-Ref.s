%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1646+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f52,f70,f73,f83,f95,f99,f103,f110,f114,f121,f128,f135,f159,f168,f176,f184])).

fof(f184,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | spl7_6
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | spl7_6
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f182,f82])).

fof(f82,plain,
    ( ~ v12_waybel_0(k3_tarski(sK1),sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_6
  <=> v12_waybel_0(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f182,plain,
    ( v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f181,f40])).

fof(f40,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl7_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f181,plain,
    ( ~ l1_orders_2(sK0)
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_3
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f51,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_3
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f178,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_20 ),
    inference(resolution,[],[f175,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f175,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_20
  <=> r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f176,plain,
    ( spl7_20
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f172,f166,f174])).

fof(f166,plain,
    ( spl7_19
  <=> sP5(sK3(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f172,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl7_19 ),
    inference(resolution,[],[f167,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f167,plain,
    ( sP5(sK3(sK0,k3_tarski(sK1)),sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl7_19
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f164,f157,f119,f166])).

fof(f119,plain,
    ( spl7_14
  <=> r2_hidden(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f157,plain,
    ( spl7_18
  <=> r2_hidden(sK3(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f164,plain,
    ( sP5(sK3(sK0,k3_tarski(sK1)),sK1)
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(resolution,[],[f161,f120])).

fof(f120,plain,
    ( r2_hidden(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK6(sK1,sK2(sK0,k3_tarski(sK1))),X1)
        | sP5(sK3(sK0,k3_tarski(sK1)),X1) )
    | ~ spl7_18 ),
    inference(resolution,[],[f158,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f158,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl7_18
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f155,f133,f126,f119,f112,f101,f93,f39,f157])).

fof(f93,plain,
    ( spl7_9
  <=> m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f101,plain,
    ( spl7_11
  <=> m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f112,plain,
    ( spl7_13
  <=> r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f126,plain,
    ( spl7_15
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f133,plain,
    ( spl7_16
  <=> m1_subset_1(sK6(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f155,plain,
    ( r2_hidden(sK3(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f154,f102])).

fof(f102,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f154,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(resolution,[],[f153,f113])).

fof(f113,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f153,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,X2,sK2(sK0,k3_tarski(sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,sK6(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f152,f94])).

fof(f94,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f152,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2(sK0,k3_tarski(sK1)))
        | r2_hidden(X2,sK6(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl7_1
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(resolution,[],[f145,f127])).

fof(f127,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK6(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK6(sK1,sK2(sK0,k3_tarski(sK1)))) )
    | ~ spl7_1
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f144,f143])).

fof(f143,plain,
    ( v12_waybel_0(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK0)
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f137,f120])).

fof(f137,plain,
    ( ~ r2_hidden(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | v12_waybel_0(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f134,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,sK1)
      | v12_waybel_0(X2,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_0)).

fof(f134,plain,
    ( m1_subset_1(sK6(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK6(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK6(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ v12_waybel_0(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK0) )
    | ~ spl7_1
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK6(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ r1_orders_2(sK0,X1,X0)
        | r2_hidden(X1,sK6(sK1,sK2(sK0,k3_tarski(sK1))))
        | ~ v12_waybel_0(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK0) )
    | ~ spl7_16 ),
    inference(resolution,[],[f134,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,
    ( spl7_16
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f131,f119,f43,f133])).

fof(f43,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f131,plain,
    ( m1_subset_1(sK6(sK1,sK2(sK0,k3_tarski(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(resolution,[],[f123,f44])).

fof(f44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f123,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | m1_subset_1(sK6(sK1,sK2(sK0,k3_tarski(sK1))),X1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f120,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f128,plain,
    ( spl7_15
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f115,f108,f126])).

fof(f108,plain,
    ( spl7_12
  <=> sP5(sK2(sK0,k3_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f115,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK6(sK1,sK2(sK0,k3_tarski(sK1))))
    | ~ spl7_12 ),
    inference(resolution,[],[f109,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(X2,sK6(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f109,plain,
    ( sP5(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f121,plain,
    ( spl7_14
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f116,f108,f119])).

fof(f116,plain,
    ( r2_hidden(sK6(sK1,sK2(sK0,k3_tarski(sK1))),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f109,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(sK6(X0,X2),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f114,plain,
    ( spl7_13
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f76,f68,f50,f43,f39,f112])).

fof(f68,plain,
    ( spl7_5
  <=> v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f76,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f61,f74])).

fof(f74,plain,
    ( ~ v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_2
    | spl7_5 ),
    inference(forward_demodulation,[],[f69,f46])).

fof(f46,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f44,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f69,plain,
    ( ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f61,plain,
    ( r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f56,f40])).

fof(f56,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3(sK0,k3_tarski(sK1)),sK2(sK0,k3_tarski(sK1)))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,X1),sK2(X0,X1))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f110,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f104,f97,f108])).

fof(f97,plain,
    ( spl7_10
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f104,plain,
    ( sP5(sK2(sK0,k3_tarski(sK1)),sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f98,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | sP5(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f98,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f103,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f78,f68,f50,f43,f39,f101])).

fof(f78,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f59,f74])).

fof(f59,plain,
    ( m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f54,f40])).

fof(f54,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK3(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f77,f68,f50,f43,f39,f97])).

fof(f77,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f60,f74])).

fof(f60,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f55,f40])).

fof(f55,plain,
    ( ~ l1_orders_2(sK0)
    | r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,
    ( spl7_9
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f75,f68,f50,f43,f39,f93])).

fof(f75,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f63,f74])).

fof(f63,plain,
    ( m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f58,f40])).

fof(f58,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK2(sK0,k3_tarski(sK1)),u1_struct_0(sK0))
    | v12_waybel_0(k3_tarski(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( ~ spl7_6
    | ~ spl7_2
    | spl7_5 ),
    inference(avatar_split_clause,[],[f74,f68,f43,f81])).

fof(f73,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(subsumption_resolution,[],[f71,f51])).

fof(f71,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | spl7_4 ),
    inference(forward_demodulation,[],[f66,f46])).

fof(f66,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_4
  <=> m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f70,plain,
    ( ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f17,f68,f65])).

fof(f17,plain,
    ( ~ v12_waybel_0(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f48,f43,f50])).

fof(f48,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f47,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2 ),
    inference(resolution,[],[f44,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f45,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------

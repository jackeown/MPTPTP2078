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
% DateTime   : Thu Dec  3 13:23:34 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  176 (1396 expanded)
%              Number of leaves         :   23 ( 457 expanded)
%              Depth                    :   26
%              Number of atoms          :  927 (12747 expanded)
%              Number of equality atoms :   24 ( 186 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f99,f141,f150,f224,f234,f240,f246,f251,f257])).

fof(f257,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f255,f97])).

fof(f97,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_2
  <=> r2_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f255,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f253,f104])).

fof(f104,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f48,f103])).

fof(f103,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f53,f102])).

fof(f102,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ r2_waybel_7(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & ( r2_waybel_7(sK0,sK1,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(sK0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & ( r2_waybel_7(sK0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_waybel_7(sK0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & ( r2_waybel_7(sK0,X1,X2)
              | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_waybel_7(sK0,sK1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & ( r2_waybel_7(sK0,sK1,X2)
            | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( ~ r2_waybel_7(sK0,sK1,X2)
          | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & ( r2_waybel_7(sK0,sK1,X2)
          | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_waybel_7(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & ( r2_waybel_7(sK0,sK1,sK2)
        | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f253,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f233,f92])).

fof(f92,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f233,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r2_waybel_7(sK0,sK1,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl3_10
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | r2_waybel_7(sK0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f251,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f249,f96])).

fof(f96,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f249,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f248,f104])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f223,f93])).

fof(f93,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f223,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ r2_waybel_7(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f246,plain,
    ( ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f244,f139])).

fof(f139,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_6
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f244,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f243,f103])).

fof(f243,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f242,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f242,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f241,f102])).

fof(f241,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f216,f157])).

fof(f157,plain,(
    ! [X3] :
      ( ~ v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f156,f107])).

fof(f107,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f106,f40])).

fof(f106,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f102])).

fof(f105,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f56,f103])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f156,plain,(
    ! [X3] :
      ( ~ v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f155,f43])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,(
    ! [X3] :
      ( ~ v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f154,f75])).

fof(f75,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f51,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f45,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f154,plain,(
    ! [X3] :
      ( ~ v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f74,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f46,f51])).

% (12761)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f46,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f153,plain,(
    ! [X3] :
      ( ~ v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f81,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f51,f51,f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f216,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_7
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f240,plain,
    ( ~ spl3_6
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl3_6
    | spl3_8 ),
    inference(subsumption_resolution,[],[f238,f139])).

fof(f238,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_8 ),
    inference(forward_demodulation,[],[f237,f103])).

fof(f237,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(subsumption_resolution,[],[f236,f40])).

fof(f236,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f235,f102])).

fof(f235,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl3_8 ),
    inference(resolution,[],[f220,f180])).

fof(f180,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f179,f107])).

fof(f179,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f178,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f177,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f176,f74])).

fof(f176,plain,(
    ! [X3] :
      ( l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f82,f73])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f69,f51,f51,f51])).

% (12757)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f69,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f220,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_8
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f234,plain,
    ( spl3_7
    | ~ spl3_8
    | spl3_10
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f230,f138,f134,f232,f218,f214])).

fof(f134,plain,
    ( spl3_5
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f230,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k2_struct_0(sK0))
        | r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f229,f103])).

fof(f229,plain,
    ( ! [X1] :
        ( r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f228,f40])).

% (12759)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f228,plain,
    ( ! [X1] :
        ( r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f227,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f227,plain,
    ( ! [X1] :
        ( r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f226,f42])).

fof(f226,plain,
    ( ! [X1] :
        ( r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f225,f136])).

fof(f136,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f225,plain,
    ( ! [X1] :
        ( r2_waybel_7(sK0,sK1,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f206,f196])).

fof(f196,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f195,f40])).

fof(f195,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f194,f102])).

fof(f194,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f193,f139])).

fof(f193,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f191,f103])).

fof(f191,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f190,f107])).

fof(f190,plain,(
    ! [X3] :
      ( v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,(
    ! [X3] :
      ( v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f188,f76])).

fof(f76,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f188,plain,(
    ! [X3] :
      ( v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f187,f75])).

fof(f187,plain,(
    ! [X3] :
      ( v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f186,f74])).

fof(f186,plain,(
    ! [X3] :
      ( v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f85,f73])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f51,f51,f51,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f206,plain,(
    ! [X1] :
      ( r2_waybel_7(sK0,sK1,X1)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f54,f204])).

fof(f204,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f203,f40])).

fof(f203,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f102])).

fof(f202,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f43])).

fof(f201,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f76])).

fof(f200,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f199,f75])).

fof(f199,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f198,f74])).

fof(f198,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f77,f73])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f51,f51,f51,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

fof(f224,plain,
    ( spl3_7
    | ~ spl3_8
    | spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f212,f138,f134,f222,f218,f214])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f211,f103])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f210,f40])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f209,f41])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f208,f42])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f207,f136])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,sK1,X0)
        | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
        | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f205,f196])).

fof(f205,plain,(
    ! [X0] :
      ( ~ r2_waybel_7(sK0,sK1,X0)
      | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f55,f204])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f150,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f148,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f148,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl3_6 ),
    inference(resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f141,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f138,f134])).

fof(f132,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f131,f40])).

fof(f131,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f102])).

fof(f130,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f128,f103])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f107])).

fof(f127,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f43])).

fof(f126,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f125,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f74])).

fof(f123,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f79,f73])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f51,f51,f51])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f49,f95,f91])).

% (12760)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f49,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f95,f91])).

fof(f50,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n010.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 18:00:59 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.36  % (12751)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.12/0.38  % (12770)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.12/0.38  % (12753)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.38  % (12753)Refutation found. Thanks to Tanya!
% 0.12/0.38  % SZS status Theorem for theBenchmark
% 0.12/0.38  % (12752)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.12/0.39  % (12750)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.12/0.39  % (12751)Refutation not found, incomplete strategy% (12751)------------------------------
% 0.12/0.39  % (12751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.39  % (12751)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.39  
% 0.12/0.39  % (12751)Memory used [KB]: 1791
% 0.12/0.39  % (12751)Time elapsed: 0.069 s
% 0.12/0.39  % (12751)------------------------------
% 0.12/0.39  % (12751)------------------------------
% 0.12/0.39  % SZS output start Proof for theBenchmark
% 0.12/0.39  fof(f258,plain,(
% 0.12/0.39    $false),
% 0.12/0.39    inference(avatar_sat_refutation,[],[f98,f99,f141,f150,f224,f234,f240,f246,f251,f257])).
% 0.12/0.39  fof(f257,plain,(
% 0.12/0.39    ~spl3_1 | spl3_2 | ~spl3_10),
% 0.12/0.39    inference(avatar_contradiction_clause,[],[f256])).
% 0.12/0.39  fof(f256,plain,(
% 0.12/0.39    $false | (~spl3_1 | spl3_2 | ~spl3_10)),
% 0.12/0.39    inference(subsumption_resolution,[],[f255,f97])).
% 0.12/0.39  fof(f97,plain,(
% 0.12/0.39    ~r2_waybel_7(sK0,sK1,sK2) | spl3_2),
% 0.12/0.39    inference(avatar_component_clause,[],[f95])).
% 0.12/0.39  fof(f95,plain,(
% 0.12/0.39    spl3_2 <=> r2_waybel_7(sK0,sK1,sK2)),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.12/0.39  fof(f255,plain,(
% 0.12/0.39    r2_waybel_7(sK0,sK1,sK2) | (~spl3_1 | ~spl3_10)),
% 0.12/0.39    inference(subsumption_resolution,[],[f253,f104])).
% 0.12/0.39  fof(f104,plain,(
% 0.12/0.39    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.12/0.39    inference(backward_demodulation,[],[f48,f103])).
% 0.12/0.39  fof(f103,plain,(
% 0.12/0.39    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.12/0.39    inference(resolution,[],[f53,f102])).
% 0.12/0.39  fof(f102,plain,(
% 0.12/0.39    l1_struct_0(sK0)),
% 0.12/0.39    inference(resolution,[],[f52,f42])).
% 0.12/0.39  fof(f42,plain,(
% 0.12/0.39    l1_pre_topc(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f35])).
% 0.12/0.39  fof(f35,plain,(
% 0.12/0.39    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.12/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.12/0.39  fof(f32,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f33,plain,(
% 0.12/0.39    ? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f34,plain,(
% 0.12/0.39    ? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f31,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f30])).
% 0.12/0.39  fof(f30,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.12/0.39    inference(nnf_transformation,[],[f15])).
% 0.12/0.39  fof(f15,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f14])).
% 0.12/0.39  fof(f14,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f13])).
% 0.12/0.39  fof(f13,negated_conjecture,(
% 0.12/0.39    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.12/0.39    inference(negated_conjecture,[],[f12])).
% 0.12/0.39  fof(f12,conjecture,(
% 0.12/0.39    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).
% 0.12/0.39  fof(f52,plain,(
% 0.12/0.39    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f16])).
% 0.12/0.39  fof(f16,plain,(
% 0.12/0.39    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f4])).
% 0.12/0.39  fof(f4,axiom,(
% 0.12/0.39    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.12/0.39  fof(f53,plain,(
% 0.12/0.39    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f17])).
% 0.12/0.39  fof(f17,plain,(
% 0.12/0.39    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f3])).
% 0.12/0.39  fof(f3,axiom,(
% 0.12/0.39    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.12/0.39  fof(f48,plain,(
% 0.12/0.39    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.12/0.39    inference(cnf_transformation,[],[f35])).
% 0.12/0.39  fof(f253,plain,(
% 0.12/0.39    ~m1_subset_1(sK2,k2_struct_0(sK0)) | r2_waybel_7(sK0,sK1,sK2) | (~spl3_1 | ~spl3_10)),
% 0.12/0.39    inference(resolution,[],[f233,f92])).
% 0.12/0.39  fof(f92,plain,(
% 0.12/0.39    r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~spl3_1),
% 0.12/0.39    inference(avatar_component_clause,[],[f91])).
% 0.12/0.39  fof(f91,plain,(
% 0.12/0.39    spl3_1 <=> r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.12/0.39  fof(f233,plain,(
% 0.12/0.39    ( ! [X1] : (~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,k2_struct_0(sK0)) | r2_waybel_7(sK0,sK1,X1)) ) | ~spl3_10),
% 0.12/0.39    inference(avatar_component_clause,[],[f232])).
% 0.12/0.39  fof(f232,plain,(
% 0.12/0.39    spl3_10 <=> ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,sK1,X1))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.12/0.39  fof(f251,plain,(
% 0.12/0.39    spl3_1 | ~spl3_2 | ~spl3_9),
% 0.12/0.39    inference(avatar_contradiction_clause,[],[f250])).
% 0.12/0.39  fof(f250,plain,(
% 0.12/0.39    $false | (spl3_1 | ~spl3_2 | ~spl3_9)),
% 0.12/0.39    inference(subsumption_resolution,[],[f249,f96])).
% 0.12/0.39  fof(f96,plain,(
% 0.12/0.39    r2_waybel_7(sK0,sK1,sK2) | ~spl3_2),
% 0.12/0.39    inference(avatar_component_clause,[],[f95])).
% 0.12/0.39  fof(f249,plain,(
% 0.12/0.39    ~r2_waybel_7(sK0,sK1,sK2) | (spl3_1 | ~spl3_9)),
% 0.12/0.39    inference(subsumption_resolution,[],[f248,f104])).
% 0.12/0.39  fof(f248,plain,(
% 0.12/0.39    ~m1_subset_1(sK2,k2_struct_0(sK0)) | ~r2_waybel_7(sK0,sK1,sK2) | (spl3_1 | ~spl3_9)),
% 0.12/0.39    inference(resolution,[],[f223,f93])).
% 0.12/0.39  fof(f93,plain,(
% 0.12/0.39    ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | spl3_1),
% 0.12/0.39    inference(avatar_component_clause,[],[f91])).
% 0.12/0.39  fof(f223,plain,(
% 0.12/0.39    ( ! [X0] : (r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_waybel_7(sK0,sK1,X0)) ) | ~spl3_9),
% 0.12/0.39    inference(avatar_component_clause,[],[f222])).
% 0.12/0.39  fof(f222,plain,(
% 0.12/0.39    spl3_9 <=> ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~r2_waybel_7(sK0,sK1,X0))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.12/0.39  fof(f246,plain,(
% 0.12/0.39    ~spl3_6 | ~spl3_7),
% 0.12/0.39    inference(avatar_contradiction_clause,[],[f245])).
% 0.12/0.39  fof(f245,plain,(
% 0.12/0.39    $false | (~spl3_6 | ~spl3_7)),
% 0.12/0.39    inference(subsumption_resolution,[],[f244,f139])).
% 0.12/0.39  fof(f139,plain,(
% 0.12/0.39    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_6),
% 0.12/0.39    inference(avatar_component_clause,[],[f138])).
% 0.12/0.39  fof(f138,plain,(
% 0.12/0.39    spl3_6 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.12/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.12/0.39  fof(f244,plain,(
% 0.12/0.39    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_7),
% 0.12/0.39    inference(forward_demodulation,[],[f243,f103])).
% 0.12/0.39  fof(f243,plain,(
% 0.12/0.39    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.12/0.39    inference(subsumption_resolution,[],[f242,f40])).
% 0.12/0.39  fof(f40,plain,(
% 0.12/0.39    ~v2_struct_0(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f35])).
% 0.12/0.39  fof(f242,plain,(
% 0.12/0.39    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl3_7),
% 0.12/0.39    inference(subsumption_resolution,[],[f241,f102])).
% 0.12/0.39  fof(f241,plain,(
% 0.12/0.39    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_7),
% 0.12/0.39    inference(resolution,[],[f216,f157])).
% 0.12/0.39  fof(f157,plain,(
% 0.12/0.39    ( ! [X3] : (~v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.39    inference(subsumption_resolution,[],[f156,f107])).
% 0.12/0.39  fof(f107,plain,(
% 0.12/0.39    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.12/0.39    inference(subsumption_resolution,[],[f106,f40])).
% 0.12/0.39  fof(f106,plain,(
% 0.12/0.39    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.12/0.39    inference(subsumption_resolution,[],[f105,f102])).
% 0.12/0.39  fof(f105,plain,(
% 0.12/0.39    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.39    inference(superposition,[],[f56,f103])).
% 0.12/0.39  fof(f56,plain,(
% 0.12/0.39    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f21])).
% 0.12/0.39  fof(f21,plain,(
% 0.12/0.39    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f20])).
% 0.12/0.39  fof(f20,plain,(
% 0.12/0.39    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f5])).
% 0.12/0.39  fof(f5,axiom,(
% 0.12/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.12/0.39  fof(f156,plain,(
% 0.12/0.39    ( ! [X3] : (~v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.39    inference(subsumption_resolution,[],[f155,f43])).
% 0.12/0.39  fof(f43,plain,(
% 0.12/0.39    ~v1_xboole_0(sK1)),
% 0.12/0.39    inference(cnf_transformation,[],[f35])).
% 0.12/0.39  fof(f155,plain,(
% 0.12/0.39    ( ! [X3] : (~v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.39    inference(subsumption_resolution,[],[f154,f75])).
% 0.12/0.39  fof(f75,plain,(
% 0.12/0.39    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.12/0.39    inference(definition_unfolding,[],[f45,f51])).
% 0.12/0.39  fof(f51,plain,(
% 0.12/0.39    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.12/0.39    inference(cnf_transformation,[],[f6])).
% 0.12/0.39  fof(f6,axiom,(
% 0.12/0.39    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.12/0.39  fof(f45,plain,(
% 0.12/0.39    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.12/0.39    inference(cnf_transformation,[],[f35])).
% 0.12/0.39  fof(f154,plain,(
% 0.12/0.39    ( ! [X3] : (~v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.39    inference(subsumption_resolution,[],[f153,f74])).
% 0.12/0.39  fof(f74,plain,(
% 0.12/0.39    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.12/0.39    inference(definition_unfolding,[],[f46,f51])).
% 0.12/0.40  % (12761)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.12/0.40  fof(f46,plain,(
% 0.12/0.40    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.12/0.40    inference(cnf_transformation,[],[f35])).
% 0.12/0.40  fof(f153,plain,(
% 0.12/0.40    ( ! [X3] : (~v2_struct_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(resolution,[],[f81,f73])).
% 0.12/0.40  fof(f73,plain,(
% 0.12/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.12/0.40    inference(definition_unfolding,[],[f47,f51])).
% 0.12/0.40  fof(f47,plain,(
% 0.12/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.12/0.40    inference(cnf_transformation,[],[f35])).
% 0.12/0.40  fof(f81,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.40    inference(definition_unfolding,[],[f63,f51,f51,f51])).
% 0.12/0.40  fof(f63,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f25])).
% 0.12/0.40  fof(f25,plain,(
% 0.12/0.40    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.40    inference(flattening,[],[f24])).
% 0.12/0.40  fof(f24,plain,(
% 0.12/0.40    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.40    inference(ennf_transformation,[],[f8])).
% 0.12/0.40  fof(f8,axiom,(
% 0.12/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.12/0.40  fof(f216,plain,(
% 0.12/0.40    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_7),
% 0.12/0.40    inference(avatar_component_clause,[],[f214])).
% 0.12/0.40  fof(f214,plain,(
% 0.12/0.40    spl3_7 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.12/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.12/0.40  fof(f240,plain,(
% 0.12/0.40    ~spl3_6 | spl3_8),
% 0.12/0.40    inference(avatar_contradiction_clause,[],[f239])).
% 0.12/0.40  fof(f239,plain,(
% 0.12/0.40    $false | (~spl3_6 | spl3_8)),
% 0.12/0.40    inference(subsumption_resolution,[],[f238,f139])).
% 0.12/0.40  fof(f238,plain,(
% 0.12/0.40    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_8),
% 0.12/0.40    inference(forward_demodulation,[],[f237,f103])).
% 0.12/0.40  fof(f237,plain,(
% 0.12/0.40    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.12/0.40    inference(subsumption_resolution,[],[f236,f40])).
% 0.12/0.40  fof(f236,plain,(
% 0.12/0.40    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl3_8),
% 0.12/0.40    inference(subsumption_resolution,[],[f235,f102])).
% 0.12/0.40  fof(f235,plain,(
% 0.12/0.40    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl3_8),
% 0.12/0.40    inference(resolution,[],[f220,f180])).
% 0.12/0.40  fof(f180,plain,(
% 0.12/0.40    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f179,f107])).
% 0.12/0.40  fof(f179,plain,(
% 0.12/0.40    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f178,f43])).
% 0.12/0.40  fof(f178,plain,(
% 0.12/0.40    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f177,f75])).
% 0.12/0.40  fof(f177,plain,(
% 0.12/0.40    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f176,f74])).
% 0.12/0.40  fof(f176,plain,(
% 0.12/0.40    ( ! [X3] : (l1_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1),X3) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.40    inference(resolution,[],[f82,f73])).
% 0.12/0.40  fof(f82,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.40    inference(definition_unfolding,[],[f69,f51,f51,f51])).
% 0.12/0.40  % (12757)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.12/0.40  fof(f69,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f27])).
% 0.12/0.40  fof(f27,plain,(
% 0.12/0.40    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.40    inference(flattening,[],[f26])).
% 0.12/0.40  fof(f26,plain,(
% 0.12/0.40    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.40    inference(ennf_transformation,[],[f7])).
% 0.12/0.40  fof(f7,axiom,(
% 0.12/0.40    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.12/0.40  fof(f220,plain,(
% 0.12/0.40    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | spl3_8),
% 0.12/0.40    inference(avatar_component_clause,[],[f218])).
% 0.12/0.40  fof(f218,plain,(
% 0.12/0.40    spl3_8 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.12/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.12/0.40  fof(f234,plain,(
% 0.12/0.40    spl3_7 | ~spl3_8 | spl3_10 | ~spl3_5 | ~spl3_6),
% 0.12/0.40    inference(avatar_split_clause,[],[f230,f138,f134,f232,f218,f214])).
% 0.12/0.40  fof(f134,plain,(
% 0.12/0.40    spl3_5 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.12/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.12/0.40  fof(f230,plain,(
% 0.12/0.40    ( ! [X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.40    inference(forward_demodulation,[],[f229,f103])).
% 0.12/0.40  fof(f229,plain,(
% 0.12/0.40    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.40    inference(subsumption_resolution,[],[f228,f40])).
% 0.12/0.40  % (12759)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.12/0.40  fof(f228,plain,(
% 0.12/0.40    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.40    inference(subsumption_resolution,[],[f227,f41])).
% 0.12/0.41  fof(f41,plain,(
% 0.12/0.41    v2_pre_topc(sK0)),
% 0.12/0.41    inference(cnf_transformation,[],[f35])).
% 0.12/0.41  fof(f227,plain,(
% 0.12/0.41    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f226,f42])).
% 0.12/0.41  fof(f226,plain,(
% 0.12/0.41    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f225,f136])).
% 0.12/0.41  fof(f136,plain,(
% 0.12/0.41    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_5),
% 0.12/0.41    inference(avatar_component_clause,[],[f134])).
% 0.12/0.41  fof(f225,plain,(
% 0.12/0.41    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f206,f196])).
% 0.12/0.41  fof(f196,plain,(
% 0.12/0.41    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f195,f40])).
% 0.12/0.41  fof(f195,plain,(
% 0.12/0.41    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f194,f102])).
% 0.12/0.41  fof(f194,plain,(
% 0.12/0.41    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f193,f139])).
% 0.12/0.41  fof(f193,plain,(
% 0.12/0.41    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(superposition,[],[f191,f103])).
% 0.12/0.41  fof(f191,plain,(
% 0.12/0.41    ( ! [X3] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f190,f107])).
% 0.12/0.41  fof(f190,plain,(
% 0.12/0.41    ( ! [X3] : (v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f189,f43])).
% 0.12/0.41  fof(f189,plain,(
% 0.12/0.41    ( ! [X3] : (v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f188,f76])).
% 0.12/0.41  fof(f76,plain,(
% 0.12/0.41    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.12/0.41    inference(definition_unfolding,[],[f44,f51])).
% 0.12/0.41  fof(f44,plain,(
% 0.12/0.41    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.12/0.41    inference(cnf_transformation,[],[f35])).
% 0.12/0.41  fof(f188,plain,(
% 0.12/0.41    ( ! [X3] : (v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f187,f75])).
% 0.12/0.41  fof(f187,plain,(
% 0.12/0.41    ( ! [X3] : (v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f186,f74])).
% 0.12/0.41  fof(f186,plain,(
% 0.12/0.41    ( ! [X3] : (v7_waybel_0(k3_yellow19(X3,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X3))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.12/0.41    inference(resolution,[],[f85,f73])).
% 0.12/0.41  fof(f85,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(definition_unfolding,[],[f72,f51,f51,f51,f51])).
% 0.12/0.41  fof(f72,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f29])).
% 0.12/0.41  fof(f29,plain,(
% 0.12/0.41    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.41    inference(flattening,[],[f28])).
% 0.12/0.41  fof(f28,plain,(
% 0.12/0.41    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.41    inference(ennf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,axiom,(
% 0.12/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.12/0.41  fof(f206,plain,(
% 0.12/0.41    ( ! [X1] : (r2_waybel_7(sK0,sK1,X1) | ~r2_hidden(X1,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.12/0.41    inference(superposition,[],[f54,f204])).
% 0.12/0.41  fof(f204,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.12/0.41    inference(subsumption_resolution,[],[f203,f40])).
% 0.12/0.41  fof(f203,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f202,f102])).
% 0.12/0.41  fof(f202,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f201,f43])).
% 0.12/0.41  fof(f201,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f200,f76])).
% 0.12/0.41  fof(f200,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f199,f75])).
% 0.12/0.41  fof(f199,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f198,f74])).
% 0.12/0.41  fof(f198,plain,(
% 0.12/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(resolution,[],[f77,f73])).
% 0.12/0.41  fof(f77,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(definition_unfolding,[],[f57,f51,f51,f51,f51])).
% 0.12/0.41  fof(f57,plain,(
% 0.12/0.41    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f23])).
% 0.12/0.41  fof(f23,plain,(
% 0.12/0.41    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.41    inference(flattening,[],[f22])).
% 0.12/0.41  fof(f22,plain,(
% 0.12/0.41    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.41    inference(ennf_transformation,[],[f11])).
% 0.12/0.41  fof(f11,axiom,(
% 0.12/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.12/0.41  fof(f54,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f36])).
% 0.12/0.41  fof(f36,plain,(
% 0.12/0.41    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.12/0.41    inference(nnf_transformation,[],[f19])).
% 0.12/0.41  fof(f19,plain,(
% 0.12/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.12/0.41    inference(flattening,[],[f18])).
% 0.12/0.41  fof(f18,plain,(
% 0.12/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.12/0.41    inference(ennf_transformation,[],[f10])).
% 0.12/0.41  fof(f10,axiom,(
% 0.12/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).
% 0.12/0.41  fof(f224,plain,(
% 0.12/0.41    spl3_7 | ~spl3_8 | spl3_9 | ~spl3_5 | ~spl3_6),
% 0.12/0.41    inference(avatar_split_clause,[],[f212,f138,f134,f222,f218,f214])).
% 0.12/0.41  fof(f212,plain,(
% 0.12/0.41    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(forward_demodulation,[],[f211,f103])).
% 0.12/0.41  fof(f211,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f210,f40])).
% 0.12/0.41  fof(f210,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f209,f41])).
% 0.12/0.41  fof(f209,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f208,f42])).
% 0.12/0.41  fof(f208,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl3_5 | ~spl3_6)),
% 0.12/0.41    inference(subsumption_resolution,[],[f207,f136])).
% 0.12/0.41  fof(f207,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f205,f196])).
% 0.12/0.41  fof(f205,plain,(
% 0.12/0.41    ( ! [X0] : (~r2_waybel_7(sK0,sK1,X0) | r2_hidden(X0,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.12/0.41    inference(superposition,[],[f55,f204])).
% 0.12/0.41  fof(f55,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f36])).
% 0.12/0.41  fof(f150,plain,(
% 0.12/0.41    spl3_6),
% 0.12/0.41    inference(avatar_contradiction_clause,[],[f149])).
% 0.12/0.41  fof(f149,plain,(
% 0.12/0.41    $false | spl3_6),
% 0.12/0.41    inference(subsumption_resolution,[],[f148,f88])).
% 0.12/0.41  fof(f88,plain,(
% 0.12/0.41    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.12/0.41    inference(equality_resolution,[],[f59])).
% 0.12/0.41  fof(f59,plain,(
% 0.12/0.41    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.12/0.41    inference(cnf_transformation,[],[f38])).
% 0.12/0.41  fof(f38,plain,(
% 0.12/0.41    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.41    inference(flattening,[],[f37])).
% 0.12/0.41  fof(f37,plain,(
% 0.12/0.41    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.41    inference(nnf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.12/0.41  fof(f148,plain,(
% 0.12/0.41    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl3_6),
% 0.12/0.41    inference(resolution,[],[f140,f62])).
% 0.12/0.41  fof(f62,plain,(
% 0.12/0.41    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f39])).
% 0.12/0.41  fof(f39,plain,(
% 0.12/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.12/0.41    inference(nnf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.12/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.12/0.41  fof(f140,plain,(
% 0.12/0.41    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_6),
% 0.12/0.41    inference(avatar_component_clause,[],[f138])).
% 0.12/0.41  fof(f141,plain,(
% 0.12/0.41    spl3_5 | ~spl3_6),
% 0.12/0.41    inference(avatar_split_clause,[],[f132,f138,f134])).
% 0.12/0.41  fof(f132,plain,(
% 0.12/0.41    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.12/0.41    inference(subsumption_resolution,[],[f131,f40])).
% 0.12/0.41  fof(f131,plain,(
% 0.12/0.41    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 0.12/0.41    inference(subsumption_resolution,[],[f130,f102])).
% 0.12/0.41  fof(f130,plain,(
% 0.12/0.41    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.12/0.41    inference(superposition,[],[f128,f103])).
% 0.12/0.41  fof(f128,plain,(
% 0.12/0.41    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f127,f107])).
% 0.12/0.41  fof(f127,plain,(
% 0.12/0.41    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f126,f43])).
% 0.12/0.41  fof(f126,plain,(
% 0.12/0.41    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f125,f75])).
% 0.12/0.41  fof(f125,plain,(
% 0.12/0.41    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(subsumption_resolution,[],[f123,f74])).
% 0.12/0.41  fof(f123,plain,(
% 0.12/0.41    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(resolution,[],[f79,f73])).
% 0.12/0.41  fof(f79,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v4_orders_2(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(definition_unfolding,[],[f65,f51,f51,f51])).
% 0.12/0.41  fof(f65,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f25])).
% 0.12/0.41  fof(f99,plain,(
% 0.12/0.41    spl3_1 | spl3_2),
% 0.12/0.41    inference(avatar_split_clause,[],[f49,f95,f91])).
% 0.12/0.41  % (12760)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.12/0.41  fof(f49,plain,(
% 0.12/0.41    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.12/0.41    inference(cnf_transformation,[],[f35])).
% 0.12/0.41  fof(f98,plain,(
% 0.12/0.41    ~spl3_1 | ~spl3_2),
% 0.12/0.41    inference(avatar_split_clause,[],[f50,f95,f91])).
% 0.12/0.41  fof(f50,plain,(
% 0.12/0.41    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.12/0.41    inference(cnf_transformation,[],[f35])).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (12753)------------------------------
% 0.12/0.41  % (12753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (12753)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (12753)Memory used [KB]: 10874
% 0.12/0.41  % (12753)Time elapsed: 0.075 s
% 0.12/0.41  % (12753)------------------------------
% 0.12/0.41  % (12753)------------------------------
% 0.12/0.41  % (12746)Success in time 0.127 s
%------------------------------------------------------------------------------

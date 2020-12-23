%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t20_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 2.61s
% Output     : Refutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 552 expanded)
%              Number of leaves         :   29 ( 209 expanded)
%              Depth                    :   23
%              Number of atoms          :  538 (3608 expanded)
%              Number of equality atoms :   51 ( 878 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10027,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f564,f574,f803,f813,f2374,f2437,f10025])).

fof(f10025,plain,
    ( ~ spl8_0
    | ~ spl8_92
    | ~ spl8_94
    | spl8_275 ),
    inference(avatar_contradiction_clause,[],[f10024])).

fof(f10024,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_92
    | ~ spl8_94
    | ~ spl8_275 ),
    inference(subsumption_resolution,[],[f10023,f793])).

fof(f793,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f792])).

fof(f792,plain,
    ( spl8_92
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f10023,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_94
    | ~ spl8_275 ),
    inference(subsumption_resolution,[],[f9994,f2373])).

fof(f2373,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ spl8_275 ),
    inference(avatar_component_clause,[],[f2372])).

fof(f2372,plain,
    ( spl8_275
  <=> ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_275])])).

fof(f9994,plain,
    ( r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl8_0
    | ~ spl8_94 ),
    inference(superposition,[],[f9527,f97])).

fof(f97,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',d3_struct_0)).

fof(f9527,plain,
    ( r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ spl8_0
    | ~ spl8_94 ),
    inference(resolution,[],[f9523,f690])).

fof(f690,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f689,f88])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f71,f70,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,sK1)
                & v2_tops_2(X2,X0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X1)
              & v2_tops_2(X2,X0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X3] :
            ( ~ v2_tops_2(X3,X1)
            & v2_tops_2(sK2,X0)
            & sK2 = X3
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_tops_2(X3,X1)
          & v2_tops_2(X2,X0)
          & X2 = X3
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ v2_tops_2(sK3,X1)
        & v2_tops_2(X2,X0)
        & sK3 = X2
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',t20_waybel_9)).

fof(f689,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f688,f509])).

fof(f509,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl8_0 ),
    inference(equality_resolution,[],[f414])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl8_0 ),
    inference(superposition,[],[f354,f90])).

fof(f90,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f72])).

fof(f354,plain,
    ( ! [X8,X7] :
        ( g1_pre_topc(X7,X8) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(sK1) = X7 )
    | ~ spl8_0 ),
    inference(resolution,[],[f117,f146])).

fof(f146,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_0
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',free_g1_pre_topc)).

fof(f688,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f687,f87])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f687,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f109,f131])).

fof(f131,plain,(
    ~ v2_tops_2(sK2,sK1) ),
    inference(forward_demodulation,[],[f93,f91])).

fof(f91,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f72])).

fof(f93,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f76,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',d2_tops_2)).

fof(f9523,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),u1_pre_topc(sK0)) )
    | ~ spl8_94 ),
    inference(subsumption_resolution,[],[f9519,f815])).

fof(f815,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_94 ),
    inference(resolution,[],[f802,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',t1_subset)).

fof(f802,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl8_94
  <=> r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f9519,plain,(
    ! [X0] :
      ( r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f2453,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',dt_k7_subset_1)).

fof(f2453,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f2450,f86])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f2450,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f2449,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',d5_pre_topc)).

fof(f2449,plain,(
    ! [X9] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X9),sK0)
      | ~ r2_hidden(X9,sK2) ) ),
    inference(subsumption_resolution,[],[f2448,f86])).

fof(f2448,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK2)
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X9),sK0) ) ),
    inference(subsumption_resolution,[],[f2444,f88])).

fof(f2444,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X9),sK0) ) ),
    inference(resolution,[],[f1382,f92])).

fof(f92,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f1382,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_tops_2(X4,X5)
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
      | ~ l1_pre_topc(X5)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),X3),X5) ) ),
    inference(subsumption_resolution,[],[f1380,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',t4_subset)).

fof(f1380,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v2_tops_2(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
      | ~ l1_pre_topc(X5)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),X3),X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(duplicate_literal_removal,[],[f1379])).

fof(f1379,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v2_tops_2(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
      | ~ l1_pre_topc(X5)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),X3),X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f1324,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',d6_pre_topc)).

fof(f1324,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f107,f127])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2437,plain,
    ( ~ spl8_54
    | spl8_273 ),
    inference(avatar_contradiction_clause,[],[f2436])).

fof(f2436,plain,
    ( $false
    | ~ spl8_54
    | ~ spl8_273 ),
    inference(subsumption_resolution,[],[f2433,f563])).

fof(f563,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl8_54
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f2433,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_273 ),
    inference(resolution,[],[f2367,f123])).

fof(f2367,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_273 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f2366,plain,
    ( spl8_273
  <=> ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_273])])).

fof(f2374,plain,
    ( ~ spl8_273
    | ~ spl8_275
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f2360,f553,f145,f2372,f2366])).

fof(f553,plain,
    ( spl8_52
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f2360,plain,
    ( ~ r2_hidden(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(resolution,[],[f2266,f684])).

fof(f684,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK1)
        | ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f683,f509])).

fof(f683,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f680,f87])).

fof(f680,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl8_0 ),
    inference(superposition,[],[f104,f673])).

fof(f673,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl8_0 ),
    inference(equality_resolution,[],[f506])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl8_0 ),
    inference(superposition,[],[f401,f90])).

fof(f401,plain,
    ( ! [X8,X7] :
        ( g1_pre_topc(X7,X8) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_pre_topc(sK1) = X8 )
    | ~ spl8_0 ),
    inference(resolution,[],[f118,f146])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f2266,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(sK1,sK2)),sK1)
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f2265,f509])).

fof(f2265,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f2250,f554])).

fof(f554,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f553])).

fof(f2250,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl8_0 ),
    inference(superposition,[],[f2245,f97])).

fof(f2245,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ spl8_0 ),
    inference(subsumption_resolution,[],[f2244,f88])).

fof(f2244,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f2243,f509])).

fof(f2243,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f2242,f509])).

fof(f2242,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f2241,f87])).

fof(f2241,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK4(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f1018,f131])).

fof(f1018,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK4(X0,X1)),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f108,f1017])).

fof(f1017,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK4(X0,X1)),X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(duplicate_literal_removal,[],[f1014])).

fof(f1014,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK4(X0,X1)),X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f106,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK4(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f813,plain,(
    spl8_93 ),
    inference(avatar_contradiction_clause,[],[f812])).

fof(f812,plain,
    ( $false
    | ~ spl8_93 ),
    inference(subsumption_resolution,[],[f811,f86])).

fof(f811,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_93 ),
    inference(resolution,[],[f796,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',dt_l1_pre_topc)).

fof(f796,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl8_93 ),
    inference(avatar_component_clause,[],[f795])).

fof(f795,plain,
    ( spl8_93
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f803,plain,
    ( ~ spl8_93
    | spl8_94
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f785,f145,f801,f795])).

fof(f785,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl8_0 ),
    inference(resolution,[],[f734,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',dt_k2_struct_0)).

fof(f734,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_0 ),
    inference(resolution,[],[f732,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',t2_subset)).

fof(f732,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0 ),
    inference(resolution,[],[f694,f88])).

fof(f694,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_0 ),
    inference(resolution,[],[f690,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',t5_subset)).

fof(f574,plain,(
    spl8_53 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f572,f87])).

fof(f572,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_53 ),
    inference(resolution,[],[f557,f100])).

fof(f557,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f556])).

fof(f556,plain,
    ( spl8_53
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f564,plain,
    ( ~ spl8_53
    | spl8_54
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f546,f145,f562,f556])).

fof(f546,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | ~ spl8_0 ),
    inference(superposition,[],[f140,f509])).

fof(f140,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f98,f97])).

fof(f159,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f157,f87])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f149,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t20_waybel_9.p',dt_u1_pre_topc)).

fof(f149,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_1
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
%------------------------------------------------------------------------------

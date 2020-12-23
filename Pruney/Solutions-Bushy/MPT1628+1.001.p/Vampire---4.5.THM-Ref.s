%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1628+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 944 expanded)
%              Number of leaves         :   15 ( 192 expanded)
%              Depth                    :   29
%              Number of atoms          :  640 (6023 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f659,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f83,f259,f295,f301,f367,f374,f651,f658])).

fof(f658,plain,
    ( ~ spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f657,f53,f63])).

fof(f63,plain,
    ( spl10_4
  <=> r2_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f53,plain,
    ( spl10_2
  <=> r1_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f657,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f22,f54])).

fof(f54,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f22,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | ~ r2_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( r1_tarski(X2,X3)
               => ( ( r2_waybel_0(X0,X1,X2)
                   => r2_waybel_0(X0,X1,X3) )
                  & ( r1_waybel_0(X0,X1,X2)
                   => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f651,plain,
    ( spl10_2
    | ~ spl10_3
    | spl10_6 ),
    inference(avatar_split_clause,[],[f649,f80,f58,f53])).

fof(f58,plain,
    ( spl10_3
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f80,plain,
    ( spl10_6
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f649,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f648,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f648,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f647,f306])).

fof(f306,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f305,f28])).

fof(f305,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f304,f27])).

fof(f27,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f304,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f303,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f303,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f302,f29])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f302,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f60,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f647,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f646,f27])).

fof(f646,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f645,f26])).

fof(f645,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f637,f29])).

fof(f637,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl10_3
    | spl10_6 ),
    inference(duplicate_literal_removal,[],[f634])).

fof(f634,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,sK3)
    | ~ spl10_3
    | spl10_6 ),
    inference(resolution,[],[f604,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f604,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK3)
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl10_3
    | spl10_6 ),
    inference(subsumption_resolution,[],[f603,f82])).

fof(f82,plain,
    ( ~ v1_xboole_0(sK3)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f603,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | v1_xboole_0(sK3)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK3) )
    | ~ spl10_3 ),
    inference(resolution,[],[f409,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f409,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK3)
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl10_3 ),
    inference(resolution,[],[f361,f67])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f361,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | r1_waybel_0(sK0,sK1,X0)
        | m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),X1) )
    | ~ spl10_3 ),
    inference(resolution,[],[f359,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f359,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f358,f308])).

fof(f308,plain,
    ( ! [X1] :
        ( m1_subset_1(sK7(sK0,sK1,X1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,X1) )
    | ~ spl10_3 ),
    inference(resolution,[],[f306,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f164,f28])).

fof(f164,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f163,f26])).

fof(f163,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f162,f29])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f358,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f357,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | ~ r1_waybel_0(sK0,sK1,sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f356,f28])).

fof(f356,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | ~ r1_waybel_0(sK0,sK1,sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f355,f27])).

fof(f355,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | ~ r1_waybel_0(sK0,sK1,sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f354,f26])).

fof(f354,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | ~ r1_waybel_0(sK0,sK1,sK2) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f353,f29])).

fof(f353,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2))),sK2)
        | ~ r1_waybel_0(sK0,sK1,sK2) )
    | ~ spl10_3 ),
    inference(resolution,[],[f307,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X4)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f307,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK6(sK0,sK1,sK2),sK7(sK0,sK1,X0,sK6(sK0,sK1,sK2)))
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl10_3 ),
    inference(resolution,[],[f306,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_orders_2(sK1,X0,sK7(sK0,sK1,X1,X0))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f192,f28])).

fof(f192,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_orders_2(sK1,X0,sK7(sK0,sK1,X1,X0))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f191,f26])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_orders_2(sK1,X0,sK7(sK0,sK1,X1,X0))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_orders_2(sK1,X0,sK7(sK0,sK1,X1,X0))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f374,plain,
    ( ~ spl10_3
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f372,f258])).

fof(f258,plain,
    ( ! [X2] : r2_waybel_0(sK0,sK1,X2)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl10_13
  <=> ! [X2] : r2_waybel_0(sK0,sK1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f372,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f22,f364])).

fof(f364,plain,
    ( ! [X2] : r1_waybel_0(sK0,sK1,X2)
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f362,f78])).

fof(f78,plain,
    ( sP9(sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_5
  <=> sP9(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f362,plain,
    ( ! [X2] :
        ( r1_waybel_0(sK0,sK1,X2)
        | ~ sP9(sK2) )
    | ~ spl10_3 ),
    inference(resolution,[],[f359,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f45,f46_D])).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f46_D])).

fof(f46_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f367,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(resolution,[],[f364,f55])).

fof(f55,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f301,plain,
    ( spl10_4
    | ~ spl10_13 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl10_4
    | ~ spl10_13 ),
    inference(resolution,[],[f258,f65])).

fof(f65,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f295,plain,
    ( ~ spl10_1
    | spl10_4
    | spl10_6 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl10_1
    | spl10_4
    | spl10_6 ),
    inference(subsumption_resolution,[],[f292,f65])).

fof(f292,plain,
    ( r2_waybel_0(sK0,sK1,sK3)
    | ~ spl10_1
    | spl10_6 ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,
    ( r2_waybel_0(sK0,sK1,sK3)
    | r2_waybel_0(sK0,sK1,sK3)
    | ~ spl10_1
    | spl10_6 ),
    inference(resolution,[],[f289,f262])).

fof(f262,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK3)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1
    | spl10_6 ),
    inference(subsumption_resolution,[],[f261,f82])).

fof(f261,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | v1_xboole_0(sK3)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f260,f41])).

fof(f260,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK3)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f254,f67])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | r2_waybel_0(sK0,sK1,X0)
        | m1_subset_1(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X1) )
    | ~ spl10_1 ),
    inference(resolution,[],[f253,f44])).

fof(f253,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK2)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f252,f29])).

fof(f252,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK2)
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f251,f28])).

fof(f251,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK2)
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f250,f27])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),sK2)
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f209,f51])).

fof(f51,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl10_1
  <=> r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,sK1,X1)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,sK1,sK5(X0,sK1,X1,sK4(sK0,sK1,X2))),X1)
      | ~ l1_struct_0(X0)
      | r2_waybel_0(sK0,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f204,f26])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,sK1,sK5(X0,sK1,X1,sK4(sK0,sK1,X2))),X1)
      | ~ r2_waybel_0(X0,sK1,X1)
      | r2_waybel_0(sK0,sK1,X2) ) ),
    inference(resolution,[],[f33,f116])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),u1_struct_0(sK1))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f115,f28])).

fof(f115,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | m1_subset_1(sK4(sK0,sK1,X0),u1_struct_0(sK1))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f114,f26])).

fof(f114,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | m1_subset_1(sK4(sK0,sK1,X0),u1_struct_0(sK1))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f113,f29])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | m1_subset_1(sK4(sK0,sK1,X0),u1_struct_0(sK1))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f288,f218])).

fof(f218,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f217,f29])).

fof(f217,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f216,f28])).

fof(f216,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f215,f27])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f142,f51])).

fof(f142,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_waybel_0(X3,sK1,X4)
      | ~ l1_waybel_0(sK1,X3)
      | v2_struct_0(X3)
      | m1_subset_1(sK5(X3,sK1,X4,sK4(sK0,sK1,X5)),u1_struct_0(sK1))
      | ~ l1_struct_0(X3)
      | r2_waybel_0(sK0,sK1,X5) ) ),
    inference(subsumption_resolution,[],[f141,f26])).

fof(f141,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_struct_0(X3)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X3)
      | v2_struct_0(X3)
      | m1_subset_1(sK5(X3,sK1,X4,sK4(sK0,sK1,X5)),u1_struct_0(sK1))
      | ~ r2_waybel_0(X3,sK1,X4)
      | r2_waybel_0(sK0,sK1,X5) ) ),
    inference(resolution,[],[f31,f116])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f288,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f287,f28])).

fof(f287,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f286,f27])).

fof(f286,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f285,f26])).

fof(f285,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f284,f29])).

fof(f284,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0) )
    | ~ spl10_1 ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0))),X0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f282,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f282,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4(sK0,sK1,X0),sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f281,f29])).

fof(f281,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK4(sK0,sK1,X0),sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f280,f28])).

fof(f280,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_orders_2(sK1,sK4(sK0,sK1,X0),sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f279,f27])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | r1_orders_2(sK1,sK4(sK0,sK1,X0),sK5(sK0,sK1,sK2,sK4(sK0,sK1,X0)))
        | ~ l1_struct_0(sK0)
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f153,f51])).

fof(f153,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_waybel_0(X3,sK1,X5)
      | ~ l1_waybel_0(sK1,X3)
      | v2_struct_0(X3)
      | r1_orders_2(sK1,sK4(sK0,sK1,X4),sK5(X3,sK1,X5,sK4(sK0,sK1,X4)))
      | ~ l1_struct_0(X3)
      | r2_waybel_0(sK0,sK1,X4) ) ),
    inference(subsumption_resolution,[],[f152,f26])).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_struct_0(X3)
      | v2_struct_0(sK1)
      | ~ l1_waybel_0(sK1,X3)
      | v2_struct_0(X3)
      | r1_orders_2(sK1,sK4(sK0,sK1,X4),sK5(X3,sK1,X5,sK4(sK0,sK1,X4)))
      | ~ r2_waybel_0(X3,sK1,X5)
      | r2_waybel_0(sK0,sK1,X4) ) ),
    inference(resolution,[],[f32,f116])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r1_orders_2(X1,X3,sK5(X0,X1,X2,X3))
      | ~ r2_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f259,plain,
    ( ~ spl10_5
    | spl10_13
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f255,f49,f257,f76])).

fof(f255,plain,
    ( ! [X2] :
        ( r2_waybel_0(sK0,sK1,X2)
        | ~ sP9(sK2) )
    | ~ spl10_1 ),
    inference(resolution,[],[f253,f47])).

fof(f83,plain,
    ( spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f74,f80,f76])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK3)
    | sP9(sK2) ),
    inference(resolution,[],[f46,f67])).

fof(f66,plain,
    ( ~ spl10_4
    | spl10_3 ),
    inference(avatar_split_clause,[],[f24,f58,f63])).

fof(f24,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ r2_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f23,f58,f49])).

fof(f23,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f21,f53,f49])).

fof(f21,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 413 expanded)
%              Number of leaves         :   13 ( 181 expanded)
%              Depth                    :   19
%              Number of atoms          :  366 (4033 expanded)
%              Number of equality atoms :   63 ( 782 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f58,f100,f185,f220])).

fof(f220,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f218,f99])).

fof(f99,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK2),sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_5
  <=> r1_tarski(k4_waybel_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f218,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK2),sK2)
    | spl4_2 ),
    inference(forward_demodulation,[],[f217,f210])).

fof(f210,plain,(
    k4_waybel_0(sK0,sK2) = k4_waybel_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f209,f22])).

fof(f22,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ~ v13_waybel_0(sK3,sK1)
        & v13_waybel_0(sK2,sK0) )
      | ( ~ v12_waybel_0(sK3,sK1)
        & v12_waybel_0(sK2,sK0) ) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v13_waybel_0(X3,X1)
                        & v13_waybel_0(X2,X0) )
                      | ( ~ v12_waybel_0(X3,X1)
                        & v12_waybel_0(X2,X0) ) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,sK0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,sK0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v13_waybel_0(X3,X1)
                    & v13_waybel_0(X2,sK0) )
                  | ( ~ v12_waybel_0(X3,X1)
                    & v12_waybel_0(X2,sK0) ) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v13_waybel_0(X3,sK1)
                  & v13_waybel_0(X2,sK0) )
                | ( ~ v12_waybel_0(X3,sK1)
                  & v12_waybel_0(X2,sK0) ) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v13_waybel_0(X3,sK1)
                & v13_waybel_0(X2,sK0) )
              | ( ~ v12_waybel_0(X3,sK1)
                & v12_waybel_0(X2,sK0) ) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ~ v13_waybel_0(X3,sK1)
              & v13_waybel_0(sK2,sK0) )
            | ( ~ v12_waybel_0(X3,sK1)
              & v12_waybel_0(sK2,sK0) ) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ( ( ~ v13_waybel_0(X3,sK1)
            & v13_waybel_0(sK2,sK0) )
          | ( ~ v12_waybel_0(X3,sK1)
            & v12_waybel_0(sK2,sK0) ) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ~ v13_waybel_0(sK3,sK1)
          & v13_waybel_0(sK2,sK0) )
        | ( ~ v12_waybel_0(sK3,sK1)
          & v12_waybel_0(sK2,sK0) ) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => ( ( v13_waybel_0(X2,X0)
                           => v13_waybel_0(X3,X1) )
                          & ( v12_waybel_0(X2,X0)
                           => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(f209,plain,
    ( k4_waybel_0(sK0,sK2) = k4_waybel_0(sK1,sK2)
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f208,f23])).

fof(f23,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,
    ( k4_waybel_0(sK0,sK2) = k4_waybel_0(sK1,sK2)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f26,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(sK0,sK2) = k4_waybel_0(X0,sK2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f91,f21])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0] :
      ( k4_waybel_0(sK0,sK2) = k4_waybel_0(X0,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ l1_orders_2(sK0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( k4_waybel_0(X1,X3) = k4_waybel_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                        & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_0)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f217,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK2),sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f174,f196])).

fof(f196,plain,
    ( ~ v13_waybel_0(sK2,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f46,f26])).

fof(f46,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_2
  <=> v13_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f174,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK2),sK2)
    | v13_waybel_0(sK2,sK1) ),
    inference(resolution,[],[f70,f59])).

fof(f70,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(k4_waybel_0(sK1,X1),X1)
      | v13_waybel_0(X1,sK1) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ~ r1_tarski(k4_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k4_waybel_0(X0,X1),X1)
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(f185,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f183,f22])).

fof(f183,plain,
    ( ~ l1_orders_2(sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f179,f23])).

fof(f179,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f150,f59])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0) )
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f149,f143])).

fof(f143,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f142,f21])).

fof(f142,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f140,f24])).

fof(f140,plain,
    ( ! [X0] :
        ( r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f83,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k3_waybel_0(X1,X3) = k3_waybel_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK2),sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f82,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK2),sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ~ r1_tarski(k3_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_0)).

fof(f51,plain,
    ( v12_waybel_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_3
  <=> v12_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f149,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0) )
    | spl4_1 ),
    inference(forward_demodulation,[],[f148,f23])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f147,f22])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f145,f59])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_waybel_0(X0,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1) )
    | spl4_1 ),
    inference(superposition,[],[f86,f38])).

fof(f86,plain,
    ( ~ r1_tarski(k3_waybel_0(sK1,sK2),sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,
    ( ~ r1_tarski(k3_waybel_0(sK1,sK2),sK2)
    | ~ l1_orders_2(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f84,f59])).

fof(f84,plain,
    ( ~ r1_tarski(k3_waybel_0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1)
    | spl4_1 ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( ~ v12_waybel_0(sK2,sK1)
    | spl4_1 ),
    inference(forward_demodulation,[],[f42,f26])).

fof(f42,plain,
    ( ~ v12_waybel_0(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> v12_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f100,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f95,f97,f54])).

fof(f54,plain,
    ( spl4_4
  <=> v13_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f87,plain,
    ( r1_tarski(k4_waybel_0(sK0,sK2),sK2)
    | ~ v13_waybel_0(sK2,sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f27,f54,f49])).

fof(f27,plain,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f28,f54,f40])).

fof(f28,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f44,f49])).

fof(f29,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f44,f40])).

fof(f30,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------

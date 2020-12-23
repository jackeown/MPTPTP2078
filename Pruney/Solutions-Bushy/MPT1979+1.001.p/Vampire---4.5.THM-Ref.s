%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:00 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  260 (1280 expanded)
%              Number of leaves         :   22 ( 472 expanded)
%              Depth                    :  125
%              Number of atoms          : 2538 (22347 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   32 (  11 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f132,f703])).

fof(f703,plain,
    ( spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f701,f120])).

fof(f120,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f701,plain,
    ( v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f700,f57])).

fof(f57,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ! [X3] :
        ( r2_hidden(sK2,X3)
        | ~ r1_tarski(sK1,X3)
        | ~ v1_waybel_7(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X3,sK0)
        | ~ v1_waybel_0(X3,sK0)
        | v1_xboole_0(X3) )
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v12_waybel_0(sK1,sK0)
    & v1_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v2_waybel_1(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v1_waybel_7(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v12_waybel_0(X3,X0)
                    | ~ v1_waybel_0(X3,X0)
                    | v1_xboole_0(X3) )
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | ~ v12_waybel_0(X3,sK0)
                  | ~ v1_waybel_0(X3,sK0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v12_waybel_0(X1,sK0)
          & v1_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v2_waybel_1(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( r2_hidden(X2,X3)
                | ~ r1_tarski(X1,X3)
                | ~ v1_waybel_7(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v12_waybel_0(X3,sK0)
                | ~ v1_waybel_0(X3,sK0)
                | v1_xboole_0(X3) )
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v12_waybel_0(X1,sK0)
        & v1_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(X2,X3)
              | ~ r1_tarski(sK1,X3)
              | ~ v1_waybel_7(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v12_waybel_0(X3,sK0)
              | ~ v1_waybel_0(X3,sK0)
              | v1_xboole_0(X3) )
          & ~ r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v12_waybel_0(sK1,sK0)
      & v1_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( r2_hidden(X2,X3)
            | ~ r1_tarski(sK1,X3)
            | ~ v1_waybel_7(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v12_waybel_0(X3,sK0)
            | ~ v1_waybel_0(X3,sK0)
            | v1_xboole_0(X3) )
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( r2_hidden(sK2,X3)
          | ~ r1_tarski(sK1,X3)
          | ~ v1_waybel_7(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v12_waybel_0(X3,sK0)
          | ~ v1_waybel_0(X3,sK0)
          | v1_xboole_0(X3) )
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r1_tarski(X1,X3)
                  | ~ v1_waybel_7(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v12_waybel_0(X3,X0)
                  | ~ v1_waybel_0(X3,X0)
                  | v1_xboole_0(X3) )
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v2_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v2_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v12_waybel_0(X3,X0)
                          & v1_waybel_0(X3,X0)
                          & ~ v1_xboole_0(X3) )
                       => ~ ( ~ r2_hidden(X2,X3)
                            & r1_tarski(X1,X3)
                            & v1_waybel_7(X3,X0) ) )
                    & ~ r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ~ r2_hidden(X2,X3)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & ~ r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_7)).

fof(f700,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f699,f63])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f699,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f698,f68])).

fof(f68,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f698,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f697,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k6_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_waybel_0)).

fof(f697,plain,
    ( v1_xboole_0(k6_waybel_0(sK0,sK2))
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f696,f68])).

fof(f696,plain,
    ( v1_xboole_0(k6_waybel_0(sK0,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f695,f69])).

fof(f69,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f695,plain,
    ( v1_xboole_0(k6_waybel_0(sK0,sK2))
    | r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f693,f185])).

fof(f185,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f184,f120])).

fof(f184,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f183,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f176,f68])).

fof(f176,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f97,f134])).

fof(f134,plain,
    ( r3_orders_2(sK0,sK2,sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f124,f68])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_3
  <=> ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f693,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK2)
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f692,f120])).

fof(f692,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f691,f63])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f690,f68])).

fof(f690,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f689])).

fof(f689,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(resolution,[],[f682,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f682,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f681,f120])).

fof(f681,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f680,f58])).

fof(f58,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f680,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f679,f63])).

fof(f679,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f678])).

fof(f678,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(resolution,[],[f677,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k6_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_waybel_0)).

fof(f677,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f676,f120])).

fof(f676,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f675,f57])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f674,f63])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f673])).

fof(f673,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(resolution,[],[f672,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k6_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f672,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f671])).

fof(f671,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | v1_xboole_0(k6_waybel_0(sK0,X0)) )
    | spl7_2 ),
    inference(resolution,[],[f670,f299])).

fof(f299,plain,
    ( ! [X0] :
        ( r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | v1_xboole_0(k6_waybel_0(sK0,X0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f297,f64])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f297,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | v1_xboole_0(sK1) )
    | spl7_2 ),
    inference(resolution,[],[f296,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f296,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,k6_waybel_0(sK0,X0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r1_xboole_0(sK1,k6_waybel_0(sK0,X0))
        | r1_xboole_0(sK1,k6_waybel_0(sK0,X0)) )
    | spl7_2 ),
    inference(resolution,[],[f286,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f286,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK6(X3,k6_waybel_0(sK0,X2)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,sK1)
        | r1_xboole_0(X3,k6_waybel_0(sK0,X2)) )
    | spl7_2 ),
    inference(resolution,[],[f283,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f283,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k6_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | r2_hidden(X1,sK1) )
    | spl7_2 ),
    inference(resolution,[],[f281,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f281,plain,
    ( ! [X0] :
        ( r1_xboole_0(k6_waybel_0(sK0,X0),sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),sK1) )
    | spl7_2 ),
    inference(resolution,[],[f279,f88])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(k6_waybel_0(sK0,X0),X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),X1) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f278,f63])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK6(k6_waybel_0(sK0,X0),X1),sK1)
        | r2_hidden(X0,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),X1)
        | ~ l1_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f277,f120])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK6(k6_waybel_0(sK0,X0),X1),sK1)
        | r2_hidden(X0,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),X1)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK6(k6_waybel_0(sK0,X0),X1),sK1)
        | r2_hidden(X0,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X0),X1)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_xboole_0(k6_waybel_0(sK0,X0),X1) )
    | spl7_2 ),
    inference(resolution,[],[f252,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(k6_waybel_0(X0,X1),X2),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_xboole_0(k6_waybel_0(X0,X1),X2) ) ),
    inference(resolution,[],[f103,f87])).

fof(f103,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k6_waybel_0(X3,X2))
      | ~ l1_orders_2(X3)
      | v2_struct_0(X3)
      | m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X2,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

fof(f252,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK6(k6_waybel_0(sK0,X2),X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(sK6(k6_waybel_0(sK0,X2),X3),sK1)
        | r2_hidden(X2,sK1)
        | r1_xboole_0(k6_waybel_0(sK0,X2),X3) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f251,f120])).

fof(f251,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(k6_waybel_0(sK0,X2),X3),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(k6_waybel_0(sK0,X2),X3),u1_struct_0(sK0))
      | r2_hidden(X2,sK1)
      | v2_struct_0(sK0)
      | r1_xboole_0(k6_waybel_0(sK0,X2),X3) ) ),
    inference(subsumption_resolution,[],[f247,f63])).

fof(f247,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(k6_waybel_0(sK0,X2),X3),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(k6_waybel_0(sK0,X2),X3),u1_struct_0(sK0))
      | r2_hidden(X2,sK1)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_xboole_0(k6_waybel_0(sK0,X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK6(k6_waybel_0(sK0,X2),X3),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK6(k6_waybel_0(sK0,X2),X3),u1_struct_0(sK0))
      | r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_xboole_0(k6_waybel_0(sK0,X2),X3) ) ),
    inference(resolution,[],[f240,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(k6_waybel_0(X0,X1),X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_xboole_0(k6_waybel_0(X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f139,f105])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(k6_waybel_0(X0,X1),X2))
      | ~ m1_subset_1(sK6(k6_waybel_0(X0,X1),X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_xboole_0(k6_waybel_0(X0,X1),X2) ) ),
    inference(resolution,[],[f78,f87])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f240,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f239,f63])).

fof(f239,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X4,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f66])).

fof(f66,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f236,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | ~ r2_hidden(X5,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v12_waybel_0(sK1,sK0)
      | r2_hidden(X4,sK1)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | r2_hidden(X5,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f670,plain,
    ( ! [X0] :
        ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f669,f120])).

fof(f669,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f668,f63])).

fof(f668,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f667])).

fof(f667,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(resolution,[],[f653,f95])).

fof(f653,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_waybel_0(sK0,X0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f652,f57])).

fof(f652,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f651,f58])).

fof(f651,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f650,f59])).

fof(f59,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f650,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f649,f60])).

fof(f60,plain,(
    v2_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f649,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f648,f61])).

fof(f61,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f648,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f647,f62])).

fof(f62,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f647,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f646,f63])).

fof(f646,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f645,f64])).

fof(f645,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f644,f65])).

fof(f65,plain,(
    v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f644,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f643,f66])).

fof(f643,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f642,f67])).

fof(f642,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(duplicate_literal_removal,[],[f641])).

fof(f641,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(k6_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_waybel_1(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | spl7_2 ),
    inference(resolution,[],[f557,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK5(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_subset_1(sK5(X0,X1,X2),X2)
                & r1_tarski(X1,sK5(X0,X1,X2))
                & v1_waybel_7(sK5(X0,X1,X2),X0)
                & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v12_waybel_0(sK5(X0,X1,X2),X0)
                & v1_waybel_0(sK5(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK5(X0,X1,X2)) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X3,X2)
          & r1_tarski(X1,X3)
          & v1_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(sK5(X0,X1,X2),X2)
        & r1_tarski(X1,sK5(X0,X1,X2))
        & v1_waybel_7(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(sK5(X0,X1,X2),X0)
        & v1_waybel_0(sK5(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X3,X2)
                  & r1_tarski(X1,X3)
                  & v1_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v12_waybel_0(X3,X0)
                        & v1_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X3,X2)
                          & r1_tarski(X1,X3)
                          & v1_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_7)).

fof(f557,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK5(sK0,sK1,k6_waybel_0(sK0,X0)))
        | v1_xboole_0(k6_waybel_0(sK0,X0))
        | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
        | ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f556,f120])).

fof(f556,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
      | v1_xboole_0(k6_waybel_0(sK0,X0))
      | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
      | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,k6_waybel_0(sK0,X0)))
      | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f553,f63])).

fof(f553,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,k6_waybel_0(sK0,X0))
      | v1_xboole_0(k6_waybel_0(sK0,X0))
      | ~ v2_waybel_0(k6_waybel_0(sK0,X0),sK0)
      | ~ v13_waybel_0(k6_waybel_0(sK0,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,k6_waybel_0(sK0,X0)))
      | ~ r2_hidden(sK2,k6_waybel_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f540,f95])).

fof(f540,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_subset_1(sK1,X0)
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f539,f57])).

fof(f539,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f538,f58])).

fof(f538,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f537,f59])).

fof(f537,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f536,f60])).

fof(f536,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f535,f61])).

fof(f535,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f534,f62])).

fof(f534,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f533,f63])).

fof(f533,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f532,f64])).

fof(f532,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f531,f65])).

fof(f531,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f530,f66])).

fof(f530,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f529,f67])).

fof(f529,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f524])).

fof(f524,plain,(
    ! [X0] :
      ( ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_subset_1(sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f523,f398])).

fof(f398,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X6,sK5(X4,X5,X3))
      | ~ v13_waybel_0(X3,X4)
      | ~ v2_waybel_0(X3,X4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v12_waybel_0(X5,X4)
      | ~ v1_waybel_0(X5,X4)
      | v1_xboole_0(X5)
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v1_lattice3(X4)
      | ~ v2_waybel_1(X4)
      | ~ v5_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | ~ r1_subset_1(X5,X3)
      | ~ r2_hidden(X6,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(resolution,[],[f339,f89])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(sK5(X2,X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v13_waybel_0(X1,X2)
      | ~ v2_waybel_0(X1,X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v12_waybel_0(X0,X2)
      | ~ v1_waybel_0(X0,X2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v1_lattice3(X2)
      | ~ v2_waybel_1(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | ~ r1_subset_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f338,f80])).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v13_waybel_0(X1,X2)
      | ~ v2_waybel_0(X1,X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v12_waybel_0(X0,X2)
      | ~ v1_waybel_0(X0,X2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v1_lattice3(X2)
      | ~ v2_waybel_1(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | r1_xboole_0(sK5(X2,X0,X1),X1)
      | v1_xboole_0(sK5(X2,X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v13_waybel_0(X1,X2)
      | ~ v2_waybel_0(X1,X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v12_waybel_0(X0,X2)
      | ~ v1_waybel_0(X0,X2)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v1_lattice3(X2)
      | ~ v2_waybel_1(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | r1_xboole_0(sK5(X2,X0,X1),X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK5(X2,X0,X1)) ) ),
    inference(resolution,[],[f86,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(sK5(X0,X1,X2),X2)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f523,plain,(
    ! [X0] :
      ( r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f522,f57])).

fof(f522,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f521,f58])).

fof(f521,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f520,f59])).

fof(f520,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f519,f60])).

fof(f519,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f518,f61])).

fof(f518,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f517,f62])).

fof(f517,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f516,f63])).

fof(f516,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f515,f64])).

fof(f515,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f514,f65])).

fof(f514,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f513,f66])).

fof(f513,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f512,f67])).

fof(f512,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f511])).

fof(f511,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f510,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v12_waybel_0(sK5(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f510,plain,(
    ! [X0] :
      ( ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v2_waybel_0(X0,sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f509,f57])).

fof(f509,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f508,f58])).

fof(f508,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f507,f59])).

fof(f507,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f506,f60])).

fof(f506,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f505,f61])).

fof(f505,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f504,f62])).

fof(f504,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f503,f63])).

fof(f503,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f502,f64])).

fof(f502,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f501,f65])).

fof(f501,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f500,f66])).

fof(f500,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f499,f67])).

fof(f499,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,(
    ! [X0] :
      ( ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f495,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f495,plain,(
    ! [X0] :
      ( ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f494,f57])).

fof(f494,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f493,f58])).

fof(f493,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f492,f59])).

fof(f492,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f491,f60])).

fof(f491,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f490,f61])).

fof(f490,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f489,f62])).

fof(f489,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f488,f63])).

fof(f488,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f487,f64])).

fof(f487,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f486,f65])).

fof(f486,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f485,f66])).

fof(f485,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f484,f67])).

fof(f484,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f483])).

fof(f483,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f456,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_waybel_7(sK5(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f456,plain,(
    ! [X0] :
      ( ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f455,f57])).

fof(f455,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f454,f58])).

fof(f454,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f453,f59])).

fof(f453,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f452,f60])).

fof(f452,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f451,f61])).

fof(f451,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f450,f62])).

fof(f450,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f449,f63])).

fof(f449,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f448,f64])).

fof(f448,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK1)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f447,f65])).

fof(f447,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f446,f66])).

fof(f446,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f445,f67])).

fof(f445,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ r1_subset_1(sK1,X0)
      | ~ v1_waybel_7(sK5(sK0,sK1,X0),sK0)
      | r2_hidden(sK2,sK5(sK0,sK1,X0))
      | ~ v12_waybel_0(sK5(sK0,sK1,X0),sK0)
      | ~ v1_waybel_0(sK5(sK0,sK1,X0),sK0)
      | v1_xboole_0(sK5(sK0,sK1,X0))
      | ~ r1_subset_1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X0,sK0)
      | ~ v2_waybel_0(X0,sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f361,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK5(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f361,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ r1_subset_1(X12,X13)
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f360,f57])).

fof(f360,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f359,f58])).

fof(f359,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f358,f59])).

fof(f358,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f357,f60])).

fof(f357,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f356,f61])).

fof(f356,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f355,f62])).

fof(f355,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(subsumption_resolution,[],[f349,f63])).

fof(f349,plain,(
    ! [X12,X13] :
      ( ~ r1_subset_1(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v13_waybel_0(X13,sK0)
      | ~ v2_waybel_0(X13,sK0)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v12_waybel_0(X12,sK0)
      | ~ v1_waybel_0(X12,sK0)
      | v1_xboole_0(X12)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v1_lattice3(sK0)
      | ~ v2_waybel_1(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r1_tarski(sK1,sK5(sK0,X12,X13))
      | ~ v1_waybel_7(sK5(sK0,X12,X13),sK0)
      | r2_hidden(sK2,sK5(sK0,X12,X13))
      | ~ v12_waybel_0(sK5(sK0,X12,X13),sK0)
      | ~ v1_waybel_0(sK5(sK0,X12,X13),sK0)
      | v1_xboole_0(sK5(sK0,X12,X13)) ) ),
    inference(resolution,[],[f83,f70])).

fof(f70,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X3)
      | ~ v1_waybel_7(X3,sK0)
      | r2_hidden(sK2,X3)
      | ~ v12_waybel_0(X3,sK0)
      | ~ v1_waybel_0(X3,sK0)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f130,f63])).

fof(f130,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f129,f62])).

fof(f129,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f121,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f121,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f128,plain,
    ( spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f127,f123,f119])).

fof(f127,plain,(
    ! [X2] :
      ( r3_orders_2(sK0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f57])).

fof(f126,plain,(
    ! [X2] :
      ( r3_orders_2(sK0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f63])).

fof(f108,plain,(
    ! [X2] :
      ( r3_orders_2(sK0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f68])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

%------------------------------------------------------------------------------

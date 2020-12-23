%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1941+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 (1001 expanded)
%              Number of leaves         :   17 ( 314 expanded)
%              Depth                    :   26
%              Number of atoms          :  529 (8749 expanded)
%              Number of equality atoms :   55 ( 222 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f225,f49,f226,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v3_pre_topc(X2,sK0)
              | ~ r2_hidden(X1,X2)
              | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & ( ( v3_pre_topc(X2,sK0)
                & r2_hidden(X1,X2) )
              | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ v3_pre_topc(X2,sK0)
            | ~ r2_hidden(sK1,X2)
            | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & ( ( v3_pre_topc(X2,sK0)
              & r2_hidden(sK1,X2) )
            | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ v3_pre_topc(X2,sK0)
          | ~ r2_hidden(sK1,X2)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & ( ( v3_pre_topc(X2,sK0)
            & r2_hidden(sK1,X2) )
          | r2_hidden(X2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(sK2,sK0)
        | ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & ( ( v3_pre_topc(sK2,sK0)
          & r2_hidden(sK1,sK2) )
        | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f110,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f100,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
          | ! [X3] :
              ( ~ v3_pre_topc(X3,X1)
              | ~ r2_hidden(X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( v3_pre_topc(sK4(X0,X1,X2),X1)
            & r2_hidden(X2,sK4(X0,X1,X2))
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_pre_topc(X4,X1)
          & r2_hidden(X2,X4)
          & X0 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v3_pre_topc(sK4(X0,X1,X2),X1)
        & r2_hidden(X2,sK4(X0,X1,X2))
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK4(X0,sK0,X1),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK4(X0,sK0,X1),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK4(X0,sK0,X1),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v3_pre_topc(sK4(X0,X1,X2),X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f226,plain,(
    r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f225,f210])).

fof(f210,plain,
    ( v3_pre_topc(sK2,sK0)
    | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(backward_demodulation,[],[f52,f208])).

fof(f208,plain,(
    u1_struct_0(k9_yellow_6(sK0,sK1)) = a_2_0_yellow_6(sK0,sK1) ),
    inference(resolution,[],[f203,f49])).

fof(f203,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | a_2_0_yellow_6(sK0,X0) = u1_struct_0(k9_yellow_6(sK0,X0)) ) ),
    inference(backward_demodulation,[],[f164,f198])).

fof(f198,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(subsumption_resolution,[],[f197,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f197,plain,(
    ! [X0] :
      ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0
      | ~ m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X8,X7] :
      ( g1_orders_2(X6,k1_yellow_1(X6)) != g1_orders_2(X7,X8)
      | u1_struct_0(g1_orders_2(X6,k1_yellow_1(X6))) = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) ) ),
    inference(superposition,[],[f71,f87])).

fof(f87,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(subsumption_resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f61,f54])).

fof(f54,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f61,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f86,plain,(
    ! [X0] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(resolution,[],[f63,f81])).

fof(f81,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f60,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f164,plain,(
    ! [X0] :
      ( u1_struct_0(k9_yellow_6(sK0,X0)) = u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f163,f80])).

fof(f163,plain,(
    ! [X0] :
      ( u1_struct_0(k9_yellow_6(sK0,X0)) = u1_struct_0(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | ~ l1_orders_2(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f62,f136])).

fof(f136,plain,(
    ! [X0] :
      ( k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k9_yellow_6(sK0,X0) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,X0),k1_yellow_1(a_2_0_yellow_6(sK0,X0))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f82,f48])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k9_yellow_6(X0,X1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_yellow_1(a_2_0_yellow_6(X0,X1))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f54])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_6)).

fof(f62,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f52,plain,
    ( v3_pre_topc(sK2,sK0)
    | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f225,plain,(
    ~ v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f224,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f224,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f223,f132])).

fof(f132,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f131,f49])).

fof(f131,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f125,f51])).

fof(f51,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,u1_struct_0(k9_yellow_6(sK0,X3)))
      | r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f120,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK0,X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f114,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK3(X0,X1,X2),X0)
                & r2_hidden(X1,sK3(X0,X1,X2))
                & sK3(X0,X1,X2) = X2
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK3(X0,X1,X2),X0)
        & r2_hidden(X1,sK3(X0,X1,X2))
        & sK3(X0,X1,X2) = X2
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,sK3(sK0,X1,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f113,f46])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,sK3(sK0,X1,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,sK3(sK0,X1,X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f223,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f219,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f150,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f47])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_0_yellow_6(sK0,X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f48])).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(X3,X1)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r2_hidden(X3,a_2_0_yellow_6(X1,X2))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f219,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f211,f132])).

fof(f211,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f53,f208])).

fof(f53,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------

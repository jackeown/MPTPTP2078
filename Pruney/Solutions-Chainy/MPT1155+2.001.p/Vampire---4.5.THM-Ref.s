%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:57 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 359 expanded)
%              Number of leaves         :   11 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          :  348 (2820 expanded)
%              Number of equality atoms :   31 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(subsumption_resolution,[],[f84,f33])).

fof(f33,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,sK4))
    & r2_hidden(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( r2_hidden(X1,k2_orders_2(X0,X2))
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(sK2,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( r2_hidden(X1,k2_orders_2(sK2,X2))
            & r2_hidden(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( r2_hidden(sK3,k2_orders_2(sK2,X2))
          & r2_hidden(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( r2_hidden(sK3,k2_orders_2(sK2,X2))
        & r2_hidden(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( r2_hidden(sK3,k2_orders_2(sK2,sK4))
      & r2_hidden(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k2_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(f84,plain,(
    ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f83,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f82,plain,(
    r2_orders_2(sK2,sK3,sK3) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,
    ( r2_orders_2(sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f78,f36])).

fof(f36,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | r2_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f76,f77])).

fof(f77,plain,(
    sK3 = sK6(sK2,sK4,sK3) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK6(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK5(X0,X1,X3))
              & r2_hidden(sK5(X0,X1,X3),X1)
              & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK6(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK6(X0,X1,X2) = X2
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK5(X0,X1,X3))
        & r2_hidden(sK5(X0,X1,X3),X1)
        & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK6(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK6(X0,X1,X2) = X2
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X3,X4)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,(
    sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    r2_hidden(sK3,k2_orders_2(sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK2,sK4))
      | sP0(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0] : sP1(X0,sK4,sK2) ),
    inference(resolution,[],[f61,f35])).

fof(f35,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f59,f30])).

fof(f30,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f58,f31])).

fof(f31,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f12,f14,f13])).

fof(f14,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK2,sK4))
      | sP0(sK2,sK4,X0)
      | ~ sP1(X0,sK4,sK2) ) ),
    inference(superposition,[],[f42,f69])).

fof(f69,plain,(
    k2_orders_2(sK2,sK4) = a_2_1_orders_2(sK2,sK4) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f64,f33])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,sK6(sK2,sK4,sK3),X0) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,sK6(X0,X1,X2),X6) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (4693)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (4689)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.20/0.52  % (4673)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.20/0.52  % (4673)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f85,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f84,f33])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    l1_orders_2(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ((r2_hidden(sK3,k2_orders_2(sK2,sK4)) & r2_hidden(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f7,f18,f17,f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK2,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK2,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (r2_hidden(sK3,k2_orders_2(sK2,X2)) & r2_hidden(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ? [X2] : (r2_hidden(sK3,k2_orders_2(sK2,X2)) & r2_hidden(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (r2_hidden(sK3,k2_orders_2(sK2,sK4)) & r2_hidden(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f7,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.20/0.52    inference(flattening,[],[f6])).
% 1.20/0.52  fof(f6,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,negated_conjecture,(
% 1.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.20/0.52    inference(negated_conjecture,[],[f4])).
% 1.20/0.52  fof(f4,conjecture,(
% 1.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 1.20/0.52  fof(f84,plain,(
% 1.20/0.52    ~l1_orders_2(sK2)),
% 1.20/0.52    inference(subsumption_resolution,[],[f83,f34])).
% 1.20/0.52  fof(f34,plain,(
% 1.20/0.52    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f83,plain,(
% 1.20/0.52    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 1.20/0.52    inference(resolution,[],[f82,f55])).
% 1.20/0.52  fof(f55,plain,(
% 1.20/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.20/0.52    inference(duplicate_literal_removal,[],[f51])).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.20/0.52    inference(equality_resolution,[],[f39])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.20/0.52    inference(flattening,[],[f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.20/0.52    inference(nnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    r2_orders_2(sK2,sK3,sK3)),
% 1.20/0.52    inference(subsumption_resolution,[],[f80,f34])).
% 1.20/0.52  fof(f80,plain,(
% 1.20/0.52    r2_orders_2(sK2,sK3,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.20/0.52    inference(resolution,[],[f78,f36])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    r2_hidden(sK3,sK4)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f78,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 1.20/0.52    inference(backward_demodulation,[],[f76,f77])).
% 1.20/0.52  fof(f77,plain,(
% 1.20/0.52    sK3 = sK6(sK2,sK4,sK3)),
% 1.20/0.52    inference(resolution,[],[f73,f45])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK6(X0,X1,X2) = X2) )),
% 1.20/0.52    inference(cnf_transformation,[],[f28])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK5(X0,X1,X3)) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK6(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f27,f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK5(X0,X1,X3)) & r2_hidden(sK5(X0,X1,X3),X1) & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK6(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.20/0.52    inference(rectify,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.20/0.52    inference(nnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.20/0.52  fof(f73,plain,(
% 1.20/0.52    sP0(sK2,sK4,sK3)),
% 1.20/0.52    inference(resolution,[],[f72,f37])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    r2_hidden(sK3,k2_orders_2(sK2,sK4))),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f72,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK2,sK4)) | sP0(sK2,sK4,X0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f71,f62])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    ( ! [X0] : (sP1(X0,sK4,sK2)) )),
% 1.20/0.52    inference(resolution,[],[f61,f35])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f61,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f60,f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ~v2_struct_0(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f60,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f59,f30])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    v3_orders_2(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f59,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f58,f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    v4_orders_2(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f58,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f57,f33])).
% 1.20/0.52  fof(f57,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(resolution,[],[f50,f32])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    v5_orders_2(sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.20/0.52    inference(definition_folding,[],[f12,f14,f13])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.20/0.52    inference(flattening,[],[f11])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.20/0.52  fof(f71,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK2,sK4)) | sP0(sK2,sK4,X0) | ~sP1(X0,sK4,sK2)) )),
% 1.20/0.52    inference(superposition,[],[f42,f69])).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    k2_orders_2(sK2,sK4) = a_2_1_orders_2(sK2,sK4)),
% 1.20/0.52    inference(resolution,[],[f68,f35])).
% 1.20/0.52  fof(f68,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f67,f29])).
% 1.20/0.52  fof(f67,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f66,f30])).
% 1.20/0.52  fof(f66,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f65,f31])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f64,f33])).
% 1.20/0.52  fof(f64,plain,(
% 1.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 1.20/0.52    inference(resolution,[],[f41,f32])).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.20/0.52    inference(flattening,[],[f9])).
% 1.20/0.52  fof(f9,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 1.20/0.52  fof(f42,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.20/0.52    inference(rectify,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.20/0.52    inference(nnf_transformation,[],[f14])).
% 1.20/0.52  fof(f76,plain,(
% 1.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,sK6(sK2,sK4,sK3),X0)) )),
% 1.20/0.52    inference(resolution,[],[f73,f46])).
% 1.20/0.52  fof(f46,plain,(
% 1.20/0.52    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,sK6(X0,X1,X2),X6)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f28])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (4673)------------------------------
% 1.20/0.52  % (4673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (4673)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (4673)Memory used [KB]: 6140
% 1.20/0.52  % (4673)Time elapsed: 0.079 s
% 1.20/0.52  % (4673)------------------------------
% 1.20/0.52  % (4673)------------------------------
% 1.20/0.52  % (4680)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.53  % (4662)Success in time 0.166 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1155+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 357 expanded)
%              Number of leaves         :   12 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (2835 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(global_subsumption,[],[f38,f64,f173,f181])).

fof(f181,plain,
    ( r2_orders_2(sK2,sK3,sK3)
    | ~ r2_hidden(sK3,sK4)
    | ~ sP0(sK2,sK4,sK3) ),
    inference(superposition,[],[f90,f179])).

fof(f179,plain,(
    sK3 = sK6(sK2,sK4,sK3) ),
    inference(resolution,[],[f173,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK6(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK5(X0,X1,X3))
        & r2_hidden(sK5(X0,X1,X3),X1)
        & m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f90,plain,(
    ! [X4,X3] :
      ( r2_orders_2(sK2,sK6(sK2,X3,X4),sK3)
      | ~ r2_hidden(sK3,X3)
      | ~ sP0(sK2,X3,X4) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( r2_hidden(sK3,k2_orders_2(sK2,sK4))
    & r2_hidden(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
    ( ? [X2] :
        ( r2_hidden(sK3,k2_orders_2(sK2,X2))
        & r2_hidden(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( r2_hidden(sK3,k2_orders_2(sK2,sK4))
      & r2_hidden(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | r2_orders_2(X0,sK6(X0,X1,X2),X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f173,plain,(
    sP0(sK2,sK4,sK3) ),
    inference(resolution,[],[f172,f39])).

fof(f39,plain,(
    r2_hidden(sK3,k2_orders_2(sK2,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f172,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK2,sK4))
      | sP0(sK2,sK4,X1) ) ),
    inference(global_subsumption,[],[f95,f170])).

fof(f170,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK2,sK4))
      | sP0(sK2,sK4,X1)
      | ~ sP1(X1,sK4,sK2) ) ),
    inference(superposition,[],[f41,f124])).

fof(f124,plain,(
    k2_orders_2(sK2,sK4) = a_2_1_orders_2(sK2,sK4) ),
    inference(resolution,[],[f123,f37])).

fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(global_subsumption,[],[f34,f33,f32,f31,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v5_orders_2(X0)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f31,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f95,plain,(
    ! [X0] : sP1(X0,sK4,sK2) ),
    inference(resolution,[],[f94,f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(global_subsumption,[],[f34,f33,f32,f31,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v5_orders_2(sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP1(X0,X2,X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f64,plain,(
    ~ r2_orders_2(sK2,sK3,sK3) ),
    inference(resolution,[],[f62,f36])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(global_subsumption,[],[f35,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(resolution,[],[f56,f57])).

fof(f57,plain,(
    sP7(sK2) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP7(X0) ) ),
    inference(cnf_transformation,[],[f55_D])).

fof(f55_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP7(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP7(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(general_splitting,[],[f50,f55_D])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f38,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------

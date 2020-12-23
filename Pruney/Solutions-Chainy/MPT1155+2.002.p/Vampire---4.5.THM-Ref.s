%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 362 expanded)
%              Number of leaves         :   12 ( 139 expanded)
%              Depth                    :   19
%              Number of atoms          :  332 (2779 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f41])).

fof(f41,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,sK5))
    & r2_hidden(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f23,f22,f21])).

fof(f21,plain,
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
              ( r2_hidden(X1,k2_orders_2(sK3,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( r2_hidden(X1,k2_orders_2(sK3,X2))
            & r2_hidden(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( r2_hidden(sK4,k2_orders_2(sK3,X2))
          & r2_hidden(sK4,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( r2_hidden(sK4,k2_orders_2(sK3,X2))
        & r2_hidden(sK4,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( r2_hidden(sK4,k2_orders_2(sK3,sK5))
      & r2_hidden(sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(f148,plain,(
    ~ r2_hidden(sK4,sK5) ),
    inference(resolution,[],[f146,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP0(sK4,sK3,X0)
      | ~ r2_hidden(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f39,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ sP0(sK4,sK3,X0) ) ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_orders_2(X1,X0,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_orders_2(X1,X0,sK7(X0,X1,X2))
          & r2_hidden(sK7(X0,X1,X2),X2)
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X0,sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X3,X1,X2] :
      ( ( sP0(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X3,X4)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X3,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X3,X1,X2] :
      ( sP0(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X3,X4)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f95,plain,(
    ~ r2_orders_2(sK3,sK4,sK4) ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f38,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,
    ( ~ r2_orders_2(sK3,sK4,sK4)
    | ~ l1_orders_2(sK3) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1) ) ),
    inference(condensation,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f146,plain,(
    sP0(sK4,sK3,sK5) ),
    inference(subsumption_resolution,[],[f145,f137])).

fof(f137,plain,(
    sP1(sK5,sK3,sK4) ),
    inference(resolution,[],[f121,f42])).

fof(f42,plain,(
    r2_hidden(sK4,k2_orders_2(sK3,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK3,sK5))
      | sP1(sK5,sK3,X0) ) ),
    inference(subsumption_resolution,[],[f119,f105])).

fof(f105,plain,(
    ! [X0] : sP2(X0,sK3,sK5) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    ! [X0] :
      ( sP2(X0,sK3,sK5)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f35,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0] :
      ( sP2(X0,sK3,sK5)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f36,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X0] :
      ( sP2(X0,sK3,sK5)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f37,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f101,plain,(
    ! [X0] :
      ( sP2(X0,sK3,sK5)
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f98,plain,(
    ! [X0] :
      ( sP2(X0,sK3,sK5)
      | ~ l1_orders_2(sK3)
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f12,f19,f18,f17])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ? [X3] :
          ( sP0(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP1(X2,X1,X0) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f40,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK3,sK5))
      | sP1(sK5,sK3,X0)
      | ~ sP2(X0,sK3,sK5) ) ),
    inference(superposition,[],[f44,f110])).

fof(f110,plain,(
    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) ),
    inference(subsumption_resolution,[],[f109,f34])).

fof(f109,plain,
    ( k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f108,f35])).

fof(f108,plain,
    ( k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f107,f36])).

fof(f107,plain,
    ( k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f106,f37])).

fof(f106,plain,
    ( k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f99,f38])).

fof(f99,plain,
    ( k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f145,plain,
    ( sP0(sK4,sK3,sK5)
    | ~ sP1(sK5,sK3,sK4) ),
    inference(superposition,[],[f48,f139])).

fof(f139,plain,(
    sK4 = sK6(sK5,sK3,sK4) ),
    inference(resolution,[],[f137,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,X1,X2) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ sP0(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP0(sK6(X0,X1,X2),X1,X0)
          & sK6(X0,X1,X2) = X2
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP0(sK6(X0,X1,X2),X1,X0)
        & sK6(X0,X1,X2) = X2
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ~ sP0(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP0(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ! [X3] :
            ( ~ sP0(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP0(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(sK6(X0,X1,X2),X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16098)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16099)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (16119)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (16105)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (16110)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16118)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (16102)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (16105)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    r2_hidden(sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ((r2_hidden(sK4,k2_orders_2(sK3,sK5)) & r2_hidden(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f23,f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK3,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(sK3,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : (r2_hidden(sK4,k2_orders_2(sK3,X2)) & r2_hidden(sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X2] : (r2_hidden(sK4,k2_orders_2(sK3,X2)) & r2_hidden(sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) => (r2_hidden(sK4,k2_orders_2(sK3,sK5)) & r2_hidden(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ~r2_hidden(sK4,sK5)),
% 0.21/0.51    inference(resolution,[],[f146,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(sK4,sK3,X0) | ~r2_hidden(sK4,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK4,X0) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~sP0(sK4,sK3,X0)) )),
% 0.21/0.51    inference(resolution,[],[f95,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_orders_2(X1,X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_orders_2(X1,X0,sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X3,X1,X2] : ((sP0(X3,X1,X2) | ? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X3,X1,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X3,X1,X2] : (sP0(X3,X1,X2) <=> ! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~r2_orders_2(sK3,sK4,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    l1_orders_2(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~r2_orders_2(sK3,sK4,sK4) | ~l1_orders_2(sK3)),
% 0.21/0.51    inference(resolution,[],[f39,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_orders_2(X1,X0,X0) | ~l1_orders_2(X1)) )),
% 0.21/0.51    inference(condensation,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => ~r2_orders_2(X0,X1,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    sP0(sK4,sK3,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    sP1(sK5,sK3,sK4)),
% 0.21/0.51    inference(resolution,[],[f121,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r2_hidden(sK4,k2_orders_2(sK3,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK3,sK5)) | sP1(sK5,sK3,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0] : (sP2(X0,sK3,sK5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (sP2(X0,sK3,sK5) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v3_orders_2(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (sP2(X0,sK3,sK5) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v4_orders_2(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X0] : (sP2(X0,sK3,sK5) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v5_orders_2(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (sP2(X0,sK3,sK5) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f38])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (sP2(X0,sK3,sK5) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.52    inference(resolution,[],[f40,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(definition_folding,[],[f12,f19,f18,f17])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> ? [X3] : (sP0(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP1(X2,X1,X0)) | ~sP2(X0,X1,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK3,sK5)) | sP1(sK5,sK3,X0) | ~sP2(X0,sK3,sK5)) )),
% 0.21/0.52    inference(superposition,[],[f44,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f34])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) | v2_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f35])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f36])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f37])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f38])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    k2_orders_2(sK3,sK5) = a_2_1_orders_2(sK3,sK5) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f40,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP2(X0,X1,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    sP0(sK4,sK3,sK5) | ~sP1(sK5,sK3,sK4)),
% 0.21/0.52    inference(superposition,[],[f48,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    sK4 = sK6(sK5,sK3,sK4)),
% 0.21/0.52    inference(resolution,[],[f137,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sK6(X0,X1,X2) = X2 | ~sP1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~sP0(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP0(sK6(X0,X1,X2),X1,X0) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (sP0(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (sP0(sK6(X0,X1,X2),X1,X0) & sK6(X0,X1,X2) = X2 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (~sP0(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP0(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ! [X3] : (~sP0(X3,X1,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP0(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X2,X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(sK6(X0,X1,X2),X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16105)------------------------------
% 0.21/0.52  % (16105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16105)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16105)Memory used [KB]: 1663
% 0.21/0.52  % (16105)Time elapsed: 0.106 s
% 0.21/0.52  % (16105)------------------------------
% 0.21/0.52  % (16105)------------------------------
% 0.21/0.52  % (16101)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (16096)Success in time 0.154 s
%------------------------------------------------------------------------------

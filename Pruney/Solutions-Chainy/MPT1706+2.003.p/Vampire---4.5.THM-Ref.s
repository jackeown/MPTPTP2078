%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 165 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  347 (1256 expanded)
%              Number of equality atoms :   73 ( 179 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f190])).

fof(f190,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f188,f53])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & m1_pre_topc(sK2,X2)
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & m1_pre_topc(sK2,X2)
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ! [X4] :
          ( sK4 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

fof(f188,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f185,f88])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f52])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f185,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | spl7_2 ),
    inference(resolution,[],[f181,f76])).

fof(f76,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f181,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | spl7_2 ),
    inference(resolution,[],[f177,f92])).

fof(f92,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f77,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f177,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k2_tarski(sK4,sK4))
        | ~ l1_pre_topc(X2)
        | m1_subset_1(X3,u1_struct_0(X2))
        | ~ m1_pre_topc(sK2,X2) )
    | spl7_2 ),
    inference(resolution,[],[f174,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f174,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_2 ),
    inference(resolution,[],[f59,f119])).

fof(f119,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f118,f103])).

fof(f103,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_2
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f118,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f117,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl7_2 ),
    inference(superposition,[],[f65,f116])).

fof(f116,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f114,f103])).

fof(f114,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f56])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f109,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f107,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f90,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f84,f48])).

fof(f84,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f104,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (15928)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:11:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15930)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15927)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (15946)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (15930)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (15951)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (15938)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f109,f190])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    spl7_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    $false | spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f188,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f34,f33,f32,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_pre_topc(sK2,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_pre_topc(sK2,X2) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ~m1_pre_topc(sK2,sK3) | spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    l1_pre_topc(sK3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f85,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f58,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_pre_topc(sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK3) | spl7_2),
% 0.21/0.52    inference(resolution,[],[f181,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.52    inference(equality_resolution,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(sK4,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | spl7_2),
% 0.21/0.52    inference(resolution,[],[f177,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 0.21/0.52    inference(resolution,[],[f77,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.52    inference(definition_folding,[],[f2,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f29])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k2_tarski(sK4,sK4)) | ~l1_pre_topc(X2) | m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(sK2,X2)) ) | spl7_2),
% 0.21/0.52    inference(resolution,[],[f174,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl7_2),
% 0.21/0.52    inference(resolution,[],[f59,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK2)) | spl7_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl7_2 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2)) | spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f117,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | spl7_2),
% 0.21/0.52    inference(superposition,[],[f65,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) | spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f103])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.52    inference(resolution,[],[f75,f54])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f64,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~spl7_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    $false | ~spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~v2_struct_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v2_struct_0(sK2) | ~spl7_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    l1_struct_0(sK2)),
% 0.21/0.52    inference(resolution,[],[f87,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    l1_pre_topc(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f48])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    l1_pre_topc(sK2) | ~l1_pre_topc(sK1)),
% 0.21/0.52    inference(resolution,[],[f58,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_pre_topc(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_2),
% 0.21/0.52    inference(resolution,[],[f104,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % (15928)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK2)) | ~spl7_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15930)------------------------------
% 0.21/0.52  % (15930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15930)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15930)Memory used [KB]: 10746
% 0.21/0.52  % (15930)Time elapsed: 0.095 s
% 0.21/0.52  % (15930)------------------------------
% 0.21/0.52  % (15930)------------------------------
% 0.21/0.52  % (15943)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (15923)Success in time 0.161 s
%------------------------------------------------------------------------------

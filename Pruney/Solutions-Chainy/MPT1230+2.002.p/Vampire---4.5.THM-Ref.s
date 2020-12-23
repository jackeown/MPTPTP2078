%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 456 expanded)
%              Number of leaves         :   12 ( 149 expanded)
%              Depth                    :   19
%              Number of atoms          :  515 (5207 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f65,f72,f79,f95,f104])).

fof(f104,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f102,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( r1_xboole_0(sK1,sK3)
        & r2_hidden(sK2,sK3)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(sK1,X4)
          | ~ r2_hidden(sK2,X4)
          | ~ v3_pre_topc(X4,sK0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15,f14,f13,f12])).

% (26004)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(X1,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(X1,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,sK0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(sK1,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(sK1,X4)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,sK0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( r1_xboole_0(sK1,X3)
              & r2_hidden(X2,X3)
              & v3_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(sK1,X4)
              | ~ r2_hidden(X2,X4)
              | ~ v3_pre_topc(X4,sK0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ? [X3] :
            ( r1_xboole_0(sK1,X3)
            & r2_hidden(sK2,X3)
            & v3_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(sK1,X4)
            | ~ r2_hidden(sK2,X4)
            | ~ v3_pre_topc(X4,sK0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( r1_xboole_0(sK1,X3)
        & r2_hidden(sK2,X3)
        & v3_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r1_xboole_0(sK1,sK3)
      & r2_hidden(sK2,sK3)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f101,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f100,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f99,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f97,f56])).

fof(f56,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f97,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK4(X0,X1,X2))
                    & r2_hidden(X2,sK4(X0,X1,X2))
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK4(X0,X1,X2))
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X4] :
                        ( ~ r1_xboole_0(X1,X4)
                        | ~ r2_hidden(X2,X4)
                        | ~ v3_pre_topc(X4,X0)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v2_struct_0(X0) )
                & ( ( ! [X3] :
                        ( ~ r1_xboole_0(X1,X3)
                        | ~ r2_hidden(X2,X3)
                        | ~ v3_pre_topc(X3,X0)
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    & ~ v2_struct_0(X0) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f40,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl5_1
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f44,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_2
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f93,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f92,f24])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f91,f84])).

fof(f84,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f29,f39])).

fof(f39,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f29,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f90,f39])).

fof(f90,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f89,f86])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f27,f39])).

fof(f27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f88,f85])).

fof(f85,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f30,f39])).

fof(f30,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X1))
      | ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f87,f25])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,X2))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X1,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f77,f23])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f76,f24])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f75,f25])).

fof(f75,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_5 ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_5 ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_5
  <=> r2_hidden(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f70,f23])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f68,f25])).

fof(f68,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f66,f40])).

fof(f66,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_4 ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f52,f38,f62,f58,f54])).

fof(f52,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,
    ( ! [X4] :
        ( ~ r1_xboole_0(sK1,X4)
        | ~ r2_hidden(sK2,X4)
        | ~ v3_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f26,f40])).

fof(f26,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(sK1,X4)
      | ~ r2_hidden(sK2,X4)
      | ~ v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,
    ( r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f50,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_xboole_0(sK1,sK4(sK0,sK1,sK2))
    | spl5_1 ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_xboole_0(X0,sK4(sK0,X0,sK2)) ) ),
    inference(resolution,[],[f48,f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_xboole_0(X0,sK4(sK0,X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,sK4(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_xboole_0(X1,sK4(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f28,f42,f38])).

fof(f28,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (26005)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (25997)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (25997)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (26012)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (26012)Refutation not found, incomplete strategy% (26012)------------------------------
% 0.22/0.50  % (26012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26012)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26012)Memory used [KB]: 895
% 0.22/0.50  % (26012)Time elapsed: 0.006 s
% 0.22/0.50  % (26012)------------------------------
% 0.22/0.50  % (26012)------------------------------
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f45,f65,f72,f79,f95,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl5_1 | spl5_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f103])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    $false | (spl5_1 | spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ((((r1_xboole_0(sK1,sK3) & r2_hidden(sK2,sK3) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(sK2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15,f14,f13,f12])).
% 0.22/0.51  % (26004)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,k2_pre_topc(sK0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,k2_pre_topc(sK0,X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,k2_pre_topc(sK0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,k2_pre_topc(sK0,X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : ((? [X3] : (r1_xboole_0(sK1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,k2_pre_topc(sK0,sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X2] : ((? [X3] : (r1_xboole_0(sK1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X2,k2_pre_topc(sK0,sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((? [X3] : (r1_xboole_0(sK1,X3) & r2_hidden(sK2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & (! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(sK2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X3] : (r1_xboole_0(sK1,X3) & r2_hidden(sK2,X3) & v3_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (r1_xboole_0(sK1,sK3) & r2_hidden(sK2,sK3) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (((? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,k2_pre_topc(X0,X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <~> ! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,plain,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.51  fof(f3,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f2])).
% 0.22/0.51  fof(f2,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (spl5_1 | spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f101,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl5_3 <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_1),
% 0.22/0.51    inference(resolution,[],[f40,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0))) & ((! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl5_1 <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~spl5_1 | ~spl5_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    $false | (~spl5_1 | ~spl5_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v3_pre_topc(sK3,sK0) | ~spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl5_2 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ~v3_pre_topc(sK3,sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f24])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f91,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    r2_hidden(sK2,sK3) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f29,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | ~spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~r2_hidden(sK2,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f90,f39])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK2,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f89,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f27,f39])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK2,sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~spl5_1),
% 0.22/0.51    inference(resolution,[],[f88,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    r1_xboole_0(sK1,sK3) | ~spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f30,f39])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    r1_xboole_0(sK1,sK3) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,k2_pre_topc(sK0,X1)) | ~r2_hidden(sK2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f87,f25])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k2_pre_topc(sK0,X2)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(X2,X1)) )),
% 0.22/0.51    inference(resolution,[],[f32,f23])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_xboole_0(X1,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl5_1 | spl5_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    $false | (spl5_1 | spl5_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f77,f23])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (spl5_1 | spl5_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f24])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f75,f25])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f74,f22])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f73,f40])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_5),
% 0.22/0.51    inference(resolution,[],[f64,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,sK4(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~r2_hidden(sK2,sK4(sK0,sK1,sK2)) | spl5_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl5_5 <=> r2_hidden(sK2,sK4(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl5_1 | spl5_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    $false | (spl5_1 | spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f23])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (spl5_1 | spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f24])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f25])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f22])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl5_1 | spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f66,f40])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_pre_topc(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_4),
% 0.22/0.51    inference(resolution,[],[f60,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v3_pre_topc(sK4(X0,X1,X2),X0) | r2_hidden(X2,k2_pre_topc(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl5_4 <=> v3_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f38,f62,f58,f54])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~r2_hidden(sK2,sK4(sK0,sK1,sK2)) | ~v3_pre_topc(sK4(sK0,sK1,sK2),sK0) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_1),
% 0.22/0.51    inference(resolution,[],[f51,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(sK2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f26,f40])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X4] : (~r1_xboole_0(sK1,X4) | ~r2_hidden(sK2,X4) | ~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,k2_pre_topc(sK0,sK1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r1_xboole_0(sK1,sK4(sK0,sK1,sK2)) | spl5_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f50,f24])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(sK1,sK4(sK0,sK1,sK2)) | spl5_1),
% 0.22/0.51    inference(resolution,[],[f49,f40])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK2,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK4(sK0,X0,sK2))) )),
% 0.22/0.51    inference(resolution,[],[f48,f25])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r1_xboole_0(X0,sK4(sK0,X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f47,f22])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,sK4(sK0,X0,X1)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,k2_pre_topc(sK0,X0))) )),
% 0.22/0.51    inference(resolution,[],[f36,f23])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | r1_xboole_0(X1,sK4(X0,X1,X2)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~spl5_1 | spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f42,f38])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    v3_pre_topc(sK3,sK0) | ~r2_hidden(sK2,k2_pre_topc(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25997)------------------------------
% 0.22/0.51  % (25997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25997)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25997)Memory used [KB]: 5373
% 0.22/0.51  % (25997)Time elapsed: 0.077 s
% 0.22/0.51  % (25997)------------------------------
% 0.22/0.51  % (25997)------------------------------
% 0.22/0.51  % (25996)Success in time 0.152 s
%------------------------------------------------------------------------------

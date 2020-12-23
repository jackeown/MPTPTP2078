%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:08 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 492 expanded)
%              Number of leaves         :   29 ( 176 expanded)
%              Depth                    :   14
%              Number of atoms          :  554 (3073 expanded)
%              Number of equality atoms :   39 (  97 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f97,f176,f181,f183,f194,f296,f344,f360,f373,f377,f378,f408,f413,f416,f454,f458])).

fof(f458,plain,
    ( ~ spl6_31
    | spl6_37
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f456,f106,f89,f356,f294])).

fof(f294,plain,
    ( spl6_31
  <=> r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f356,plain,
    ( spl6_37
  <=> r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f89,plain,
    ( spl6_1
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f106,plain,
    ( spl6_4
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f456,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f431,f209])).

fof(f209,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(sK2,sK0,X0)
      | r1_tarski(X0,k1_tops_1(sK0,sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f145,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,X0) ) ),
    inference(global_subsumption,[],[f55,f56,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(sK2,sK0,X0)
      | r1_tarski(X0,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f431,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f95,f107])).

fof(f107,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f95,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f454,plain,
    ( spl6_16
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | spl6_16
    | ~ spl6_37 ),
    inference(resolution,[],[f445,f86])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

% (9553)Refutation not found, incomplete strategy% (9553)------------------------------
% (9553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f49])).

% (9544)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f445,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl6_16
    | ~ spl6_37 ),
    inference(resolution,[],[f365,f359])).

fof(f359,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl6_16
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f365,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ r2_hidden(X0,k1_tarski(sK1)) )
    | ~ spl6_37 ),
    inference(resolution,[],[f357,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f357,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f356])).

fof(f416,plain,(
    spl6_45 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl6_45 ),
    inference(subsumption_resolution,[],[f56,f409])).

fof(f409,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_45 ),
    inference(resolution,[],[f407,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f407,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl6_45
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f413,plain,
    ( spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f178,f103,f110])).

fof(f110,plain,
    ( spl6_5
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f103,plain,
    ( spl6_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f178,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f57,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f408,plain,
    ( spl6_7
    | ~ spl6_45
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f404,f103,f406,f121])).

fof(f121,plain,
    ( spl6_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f404,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f104,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f378,plain,
    ( ~ spl6_10
    | spl6_2
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f196,f192,f92,f130])).

fof(f130,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f92,plain,
    ( spl6_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f196,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(resolution,[],[f148,f193])).

fof(f193,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f148,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f54,f55,f56,f139])).

fof(f139,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_tops_1(sK0,sK2))
      | m1_connsp_2(sK2,sK0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f377,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f186,f368])).

fof(f368,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl6_38
  <=> m2_connsp_2(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f186,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f90,f107])).

fof(f90,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f373,plain,
    ( ~ spl6_31
    | spl6_38
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f364,f356,f367,f294])).

fof(f364,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(resolution,[],[f357,f228])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f146,f84])).

fof(f146,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(sK2,sK0,X1)
      | ~ r1_tarski(X1,k1_tops_1(sK0,sK2)) ) ),
    inference(global_subsumption,[],[f55,f56,f137])).

% (9549)Refutation not found, incomplete strategy% (9549)------------------------------
% (9549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9549)Termination reason: Refutation not found, incomplete strategy

% (9549)Memory used [KB]: 11001
% (9549)Time elapsed: 0.110 s
% (9549)------------------------------
% (9549)------------------------------
% (9553)Termination reason: Refutation not found, incomplete strategy

% (9553)Memory used [KB]: 10746
% (9553)Time elapsed: 0.135 s
% (9553)------------------------------
% (9553)------------------------------
% (9538)Termination reason: Refutation not found, incomplete strategy

% (9538)Memory used [KB]: 10746
% (9538)Time elapsed: 0.135 s
% (9538)------------------------------
% (9538)------------------------------
fof(f137,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_tops_1(sK0,sK2))
      | m2_connsp_2(sK2,sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f360,plain,
    ( spl6_37
    | ~ spl6_16
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f354,f291,f192,f356])).

fof(f291,plain,
    ( spl6_30
  <=> r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f354,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ spl6_30 ),
    inference(superposition,[],[f78,f345])).

fof(f345,plain,
    ( sK1 = sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ spl6_30 ),
    inference(resolution,[],[f292,f87])).

fof(f87,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f292,plain,
    ( r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f291])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f344,plain,
    ( spl6_31
    | ~ spl6_5
    | spl6_31 ),
    inference(avatar_split_clause,[],[f338,f294,f110,f294])).

fof(f338,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | spl6_31 ),
    inference(superposition,[],[f78,f334])).

fof(f334,plain,
    ( sK1 = sK4(k1_tarski(sK1),u1_struct_0(sK0))
    | spl6_31 ),
    inference(resolution,[],[f311,f87])).

fof(f311,plain,
    ( r2_hidden(sK4(k1_tarski(sK1),u1_struct_0(sK0)),k1_tarski(sK1))
    | spl6_31 ),
    inference(resolution,[],[f295,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f295,plain,
    ( ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl6_30
    | ~ spl6_31
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f285,f106,f89,f294,f291])).

fof(f285,plain,
    ( ~ r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1))
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f262,f186])).

fof(f262,plain,(
    ! [X0] :
      ( m2_connsp_2(sK2,sK0,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | r2_hidden(sK4(X0,k1_tops_1(sK0,sK2)),X0) ) ),
    inference(resolution,[],[f228,f77])).

fof(f194,plain,
    ( ~ spl6_10
    | spl6_16
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f190,f92,f192,f130])).

fof(f190,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(resolution,[],[f147,f96])).

fof(f96,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f147,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK2,sK0,X2)
      | r2_hidden(X2,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f54,f55,f56,f138])).

fof(f138,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK2,sK0,X2)
      | r2_hidden(X2,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f183,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f54,f122])).

fof(f122,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f181,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f177,f106,f103])).

fof(f177,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f57,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f176,plain,
    ( spl6_3
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f172,f130,f110,f103])).

fof(f172,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl6_10 ),
    inference(resolution,[],[f131,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f131,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f97,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f59,f92,f89])).

fof(f59,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f60,f92,f89])).

fof(f60,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:22:23 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (9532)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.51  % (9546)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.16/0.51  % (9549)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.16/0.51  % (9531)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.52  % (9541)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.16/0.52  % (9536)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.16/0.52  % (9543)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.16/0.52  % (9530)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.16/0.52  % (9533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.52  % (9535)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.16/0.53  % (9538)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.16/0.53  % (9540)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.16/0.53  % (9551)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.16/0.53  % (9553)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.16/0.53  % (9537)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.16/0.53  % (9556)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.16/0.53  % (9554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.16/0.53  % (9537)Refutation not found, incomplete strategy% (9537)------------------------------
% 1.16/0.53  % (9537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (9537)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (9537)Memory used [KB]: 10746
% 1.16/0.53  % (9537)Time elapsed: 0.122 s
% 1.16/0.53  % (9537)------------------------------
% 1.16/0.53  % (9537)------------------------------
% 1.16/0.53  % (9529)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.53  % (9548)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.16/0.54  % (9528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.54  % (9539)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (9531)Refutation not found, incomplete strategy% (9531)------------------------------
% 1.39/0.54  % (9531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (9531)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (9531)Memory used [KB]: 6396
% 1.39/0.54  % (9531)Time elapsed: 0.138 s
% 1.39/0.54  % (9531)------------------------------
% 1.39/0.54  % (9531)------------------------------
% 1.39/0.54  % (9527)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (9552)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.54  % (9550)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  % (9542)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.54  % (9547)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (9545)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (9538)Refutation not found, incomplete strategy% (9538)------------------------------
% 1.39/0.55  % (9538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (9555)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.56  % (9529)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f459,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(avatar_sat_refutation,[],[f94,f97,f176,f181,f183,f194,f296,f344,f360,f373,f377,f378,f408,f413,f416,f454,f458])).
% 1.39/0.56  fof(f458,plain,(
% 1.39/0.56    ~spl6_31 | spl6_37 | ~spl6_1 | ~spl6_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f456,f106,f89,f356,f294])).
% 1.39/0.56  fof(f294,plain,(
% 1.39/0.56    spl6_31 <=> r1_tarski(k1_tarski(sK1),u1_struct_0(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.39/0.56  fof(f356,plain,(
% 1.39/0.56    spl6_37 <=> r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    spl6_1 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.39/0.56  fof(f106,plain,(
% 1.39/0.56    spl6_4 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.39/0.56  fof(f456,plain,(
% 1.39/0.56    r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl6_1 | ~spl6_4)),
% 1.39/0.56    inference(resolution,[],[f431,f209])).
% 1.39/0.56  fof(f209,plain,(
% 1.39/0.56    ( ! [X0] : (~m2_connsp_2(sK2,sK0,X0) | r1_tarski(X0,k1_tops_1(sK0,sK2)) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 1.39/0.56    inference(resolution,[],[f145,f84])).
% 1.39/0.56  fof(f84,plain,(
% 1.39/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f53])).
% 1.39/0.56  fof(f53,plain,(
% 1.39/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.56    inference(nnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.56  fof(f145,plain,(
% 1.39/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_tops_1(sK0,sK2)) | ~m2_connsp_2(sK2,sK0,X0)) )),
% 1.39/0.56    inference(global_subsumption,[],[f55,f56,f136])).
% 1.39/0.56  fof(f136,plain,(
% 1.39/0.56    ( ! [X0] : (~m2_connsp_2(sK2,sK0,X0) | r1_tarski(X0,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.39/0.56    inference(resolution,[],[f58,f65])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.56    inference(flattening,[],[f22])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f35,plain,(
% 1.39/0.56    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f36,plain,(
% 1.39/0.56    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f32])).
% 1.39/0.56  fof(f32,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f16])).
% 1.39/0.56  fof(f16,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f15])).
% 1.39/0.56  fof(f15,plain,(
% 1.39/0.56    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f14])).
% 1.39/0.56  fof(f14,negated_conjecture,(
% 1.39/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.39/0.56    inference(negated_conjecture,[],[f13])).
% 1.39/0.56  fof(f13,conjecture,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    l1_pre_topc(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    v2_pre_topc(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f431,plain,(
% 1.39/0.56    m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | (~spl6_1 | ~spl6_4)),
% 1.39/0.56    inference(backward_demodulation,[],[f95,f107])).
% 1.39/0.56  fof(f107,plain,(
% 1.39/0.56    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl6_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f106])).
% 1.39/0.56  fof(f95,plain,(
% 1.39/0.56    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl6_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f89])).
% 1.39/0.56  fof(f454,plain,(
% 1.39/0.56    spl6_16 | ~spl6_37),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f453])).
% 1.39/0.56  fof(f453,plain,(
% 1.39/0.56    $false | (spl6_16 | ~spl6_37)),
% 1.39/0.56    inference(resolution,[],[f445,f86])).
% 1.39/0.56  fof(f86,plain,(
% 1.39/0.56    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.39/0.56    inference(equality_resolution,[],[f85])).
% 1.39/0.56  fof(f85,plain,(
% 1.39/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.39/0.56    inference(equality_resolution,[],[f80])).
% 1.39/0.56  fof(f80,plain,(
% 1.39/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  % (9553)Refutation not found, incomplete strategy% (9553)------------------------------
% 1.39/0.56  % (9553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  fof(f52,plain,(
% 1.39/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f50,f51])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.56    inference(rectify,[],[f49])).
% 1.39/0.56  % (9544)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.56  fof(f49,plain,(
% 1.39/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.56    inference(nnf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.39/0.56  fof(f445,plain,(
% 1.39/0.56    ~r2_hidden(sK1,k1_tarski(sK1)) | (spl6_16 | ~spl6_37)),
% 1.39/0.56    inference(resolution,[],[f365,f359])).
% 1.39/0.56  fof(f359,plain,(
% 1.39/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl6_16),
% 1.39/0.56    inference(avatar_component_clause,[],[f192])).
% 1.39/0.56  fof(f192,plain,(
% 1.39/0.56    spl6_16 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.39/0.56  fof(f365,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(X0,k1_tops_1(sK0,sK2)) | ~r2_hidden(X0,k1_tarski(sK1))) ) | ~spl6_37),
% 1.39/0.56    inference(resolution,[],[f357,f76])).
% 1.39/0.56  fof(f76,plain,(
% 1.39/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f48])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(rectify,[],[f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(nnf_transformation,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f2])).
% 1.39/0.56  fof(f2,axiom,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.56  fof(f357,plain,(
% 1.39/0.56    r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~spl6_37),
% 1.39/0.56    inference(avatar_component_clause,[],[f356])).
% 1.39/0.56  fof(f416,plain,(
% 1.39/0.56    spl6_45),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f415])).
% 1.39/0.56  fof(f415,plain,(
% 1.39/0.56    $false | spl6_45),
% 1.39/0.56    inference(subsumption_resolution,[],[f56,f409])).
% 1.39/0.56  fof(f409,plain,(
% 1.39/0.56    ~l1_pre_topc(sK0) | spl6_45),
% 1.39/0.56    inference(resolution,[],[f407,f61])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f17])).
% 1.39/0.56  fof(f17,plain,(
% 1.39/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f7])).
% 1.39/0.56  fof(f7,axiom,(
% 1.39/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.39/0.56  fof(f407,plain,(
% 1.39/0.56    ~l1_struct_0(sK0) | spl6_45),
% 1.39/0.56    inference(avatar_component_clause,[],[f406])).
% 1.39/0.56  fof(f406,plain,(
% 1.39/0.56    spl6_45 <=> l1_struct_0(sK0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.39/0.56  fof(f413,plain,(
% 1.39/0.56    spl6_5 | spl6_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f178,f103,f110])).
% 1.39/0.56  fof(f110,plain,(
% 1.39/0.56    spl6_5 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.39/0.56  fof(f103,plain,(
% 1.39/0.56    spl6_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.39/0.56  fof(f178,plain,(
% 1.39/0.56    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 1.39/0.56    inference(resolution,[],[f57,f73])).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f26])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.39/0.56    inference(flattening,[],[f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f408,plain,(
% 1.39/0.56    spl6_7 | ~spl6_45 | ~spl6_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f404,f103,f406,f121])).
% 1.39/0.56  fof(f121,plain,(
% 1.39/0.56    spl6_7 <=> v2_struct_0(sK0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.39/0.56  fof(f404,plain,(
% 1.39/0.56    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_3),
% 1.39/0.56    inference(resolution,[],[f104,f62])).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,plain,(
% 1.39/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f18])).
% 1.39/0.56  fof(f18,plain,(
% 1.39/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.39/0.56  fof(f104,plain,(
% 1.39/0.56    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f103])).
% 1.39/0.56  fof(f378,plain,(
% 1.39/0.56    ~spl6_10 | spl6_2 | ~spl6_16),
% 1.39/0.56    inference(avatar_split_clause,[],[f196,f192,f92,f130])).
% 1.39/0.56  fof(f130,plain,(
% 1.39/0.56    spl6_10 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    spl6_2 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.39/0.56  fof(f196,plain,(
% 1.39/0.56    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_16),
% 1.39/0.56    inference(resolution,[],[f148,f193])).
% 1.39/0.56  fof(f193,plain,(
% 1.39/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl6_16),
% 1.39/0.56    inference(avatar_component_clause,[],[f192])).
% 1.39/0.56  fof(f148,plain,(
% 1.39/0.56    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 1.39/0.56    inference(global_subsumption,[],[f54,f55,f56,f139])).
% 1.39/0.56  fof(f139,plain,(
% 1.39/0.56    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK2)) | m1_connsp_2(sK2,sK0,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.56    inference(resolution,[],[f58,f64])).
% 1.39/0.56  fof(f64,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(nnf_transformation,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.56    inference(flattening,[],[f20])).
% 1.39/0.56  fof(f20,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f10])).
% 1.39/0.56  fof(f10,axiom,(
% 1.39/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.39/0.56  fof(f54,plain,(
% 1.39/0.56    ~v2_struct_0(sK0)),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f377,plain,(
% 1.39/0.56    spl6_1 | ~spl6_4 | ~spl6_38),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f374])).
% 1.39/0.56  fof(f374,plain,(
% 1.39/0.56    $false | (spl6_1 | ~spl6_4 | ~spl6_38)),
% 1.39/0.56    inference(subsumption_resolution,[],[f186,f368])).
% 1.39/0.56  fof(f368,plain,(
% 1.39/0.56    m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~spl6_38),
% 1.39/0.56    inference(avatar_component_clause,[],[f367])).
% 1.39/0.56  fof(f367,plain,(
% 1.39/0.56    spl6_38 <=> m2_connsp_2(sK2,sK0,k1_tarski(sK1))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.39/0.56  fof(f186,plain,(
% 1.39/0.56    ~m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | (spl6_1 | ~spl6_4)),
% 1.39/0.56    inference(backward_demodulation,[],[f90,f107])).
% 1.39/0.56  fof(f90,plain,(
% 1.39/0.56    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl6_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f89])).
% 1.39/0.56  fof(f373,plain,(
% 1.39/0.56    ~spl6_31 | spl6_38 | ~spl6_37),
% 1.39/0.56    inference(avatar_split_clause,[],[f364,f356,f367,f294])).
% 1.39/0.56  fof(f364,plain,(
% 1.39/0.56    m2_connsp_2(sK2,sK0,k1_tarski(sK1)) | ~r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) | ~spl6_37),
% 1.39/0.56    inference(resolution,[],[f357,f228])).
% 1.39/0.56  fof(f228,plain,(
% 1.39/0.56    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 1.39/0.56    inference(resolution,[],[f146,f84])).
% 1.39/0.56  fof(f146,plain,(
% 1.39/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,X1) | ~r1_tarski(X1,k1_tops_1(sK0,sK2))) )),
% 1.39/0.56    inference(global_subsumption,[],[f55,f56,f137])).
% 1.39/0.56  % (9549)Refutation not found, incomplete strategy% (9549)------------------------------
% 1.39/0.56  % (9549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9549)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9549)Memory used [KB]: 11001
% 1.39/0.56  % (9549)Time elapsed: 0.110 s
% 1.39/0.56  % (9549)------------------------------
% 1.39/0.56  % (9549)------------------------------
% 1.39/0.56  % (9553)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9553)Memory used [KB]: 10746
% 1.39/0.56  % (9553)Time elapsed: 0.135 s
% 1.39/0.56  % (9553)------------------------------
% 1.39/0.56  % (9553)------------------------------
% 1.39/0.56  % (9538)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9538)Memory used [KB]: 10746
% 1.39/0.56  % (9538)Time elapsed: 0.135 s
% 1.39/0.56  % (9538)------------------------------
% 1.39/0.56  % (9538)------------------------------
% 1.39/0.56  fof(f137,plain,(
% 1.39/0.56    ( ! [X1] : (~r1_tarski(X1,k1_tops_1(sK0,sK2)) | m2_connsp_2(sK2,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.39/0.56    inference(resolution,[],[f58,f66])).
% 1.39/0.56  fof(f66,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f39])).
% 1.39/0.56  fof(f360,plain,(
% 1.39/0.56    spl6_37 | ~spl6_16 | ~spl6_30),
% 1.39/0.56    inference(avatar_split_clause,[],[f354,f291,f192,f356])).
% 1.39/0.56  fof(f291,plain,(
% 1.39/0.56    spl6_30 <=> r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1))),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.39/0.56  fof(f354,plain,(
% 1.39/0.56    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~spl6_30),
% 1.39/0.56    inference(superposition,[],[f78,f345])).
% 1.39/0.56  fof(f345,plain,(
% 1.39/0.56    sK1 = sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | ~spl6_30),
% 1.39/0.56    inference(resolution,[],[f292,f87])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.39/0.56    inference(equality_resolution,[],[f79])).
% 1.39/0.56  fof(f79,plain,(
% 1.39/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f52])).
% 1.39/0.56  fof(f292,plain,(
% 1.39/0.56    r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1)) | ~spl6_30),
% 1.39/0.56    inference(avatar_component_clause,[],[f291])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f48])).
% 1.39/0.56  fof(f344,plain,(
% 1.39/0.56    spl6_31 | ~spl6_5 | spl6_31),
% 1.39/0.56    inference(avatar_split_clause,[],[f338,f294,f110,f294])).
% 1.39/0.56  fof(f338,plain,(
% 1.39/0.56    ~r2_hidden(sK1,u1_struct_0(sK0)) | r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) | spl6_31),
% 1.39/0.56    inference(superposition,[],[f78,f334])).
% 1.39/0.56  fof(f334,plain,(
% 1.39/0.56    sK1 = sK4(k1_tarski(sK1),u1_struct_0(sK0)) | spl6_31),
% 1.39/0.56    inference(resolution,[],[f311,f87])).
% 1.39/0.56  fof(f311,plain,(
% 1.39/0.56    r2_hidden(sK4(k1_tarski(sK1),u1_struct_0(sK0)),k1_tarski(sK1)) | spl6_31),
% 1.39/0.56    inference(resolution,[],[f295,f77])).
% 1.39/0.56  fof(f77,plain,(
% 1.39/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f48])).
% 1.39/0.56  fof(f295,plain,(
% 1.39/0.56    ~r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) | spl6_31),
% 1.39/0.56    inference(avatar_component_clause,[],[f294])).
% 1.39/0.56  fof(f296,plain,(
% 1.39/0.56    spl6_30 | ~spl6_31 | spl6_1 | ~spl6_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f285,f106,f89,f294,f291])).
% 1.39/0.56  fof(f285,plain,(
% 1.39/0.56    ~r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) | r2_hidden(sK4(k1_tarski(sK1),k1_tops_1(sK0,sK2)),k1_tarski(sK1)) | (spl6_1 | ~spl6_4)),
% 1.39/0.56    inference(resolution,[],[f262,f186])).
% 1.39/0.56  fof(f262,plain,(
% 1.39/0.56    ( ! [X0] : (m2_connsp_2(sK2,sK0,X0) | ~r1_tarski(X0,u1_struct_0(sK0)) | r2_hidden(sK4(X0,k1_tops_1(sK0,sK2)),X0)) )),
% 1.39/0.56    inference(resolution,[],[f228,f77])).
% 1.39/0.56  fof(f194,plain,(
% 1.39/0.56    ~spl6_10 | spl6_16 | ~spl6_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f190,f92,f192,f130])).
% 1.39/0.56  fof(f190,plain,(
% 1.39/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_2),
% 1.39/0.56    inference(resolution,[],[f147,f96])).
% 1.39/0.56  fof(f96,plain,(
% 1.39/0.56    m1_connsp_2(sK2,sK0,sK1) | ~spl6_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f92])).
% 1.39/0.56  fof(f147,plain,(
% 1.39/0.56    ( ! [X2] : (~m1_connsp_2(sK2,sK0,X2) | r2_hidden(X2,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.39/0.56    inference(global_subsumption,[],[f54,f55,f56,f138])).
% 1.39/0.56  fof(f138,plain,(
% 1.39/0.56    ( ! [X2] : (~m1_connsp_2(sK2,sK0,X2) | r2_hidden(X2,k1_tops_1(sK0,sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.39/0.56    inference(resolution,[],[f58,f63])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f38])).
% 1.39/0.56  fof(f183,plain,(
% 1.39/0.56    ~spl6_7),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f182])).
% 1.39/0.56  fof(f182,plain,(
% 1.39/0.56    $false | ~spl6_7),
% 1.39/0.56    inference(subsumption_resolution,[],[f54,f122])).
% 1.39/0.56  fof(f122,plain,(
% 1.39/0.56    v2_struct_0(sK0) | ~spl6_7),
% 1.39/0.56    inference(avatar_component_clause,[],[f121])).
% 1.39/0.56  fof(f181,plain,(
% 1.39/0.56    spl6_3 | spl6_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f177,f106,f103])).
% 1.39/0.56  fof(f177,plain,(
% 1.39/0.56    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 1.39/0.56    inference(resolution,[],[f57,f75])).
% 1.39/0.56  fof(f75,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f30])).
% 1.39/0.56  fof(f30,plain,(
% 1.39/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.39/0.56    inference(flattening,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f9])).
% 1.39/0.56  fof(f9,axiom,(
% 1.39/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.39/0.56  fof(f176,plain,(
% 1.39/0.56    spl6_3 | ~spl6_5 | spl6_10),
% 1.39/0.56    inference(avatar_split_clause,[],[f172,f130,f110,f103])).
% 1.39/0.56  fof(f172,plain,(
% 1.39/0.56    ~r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl6_10),
% 1.39/0.56    inference(resolution,[],[f131,f70])).
% 1.39/0.56  fof(f70,plain,(
% 1.39/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.39/0.56    inference(nnf_transformation,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.39/0.56  fof(f131,plain,(
% 1.39/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_10),
% 1.39/0.56    inference(avatar_component_clause,[],[f130])).
% 1.39/0.56  fof(f97,plain,(
% 1.39/0.56    spl6_1 | spl6_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f59,f92,f89])).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  fof(f94,plain,(
% 1.39/0.56    ~spl6_1 | ~spl6_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f60,f92,f89])).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.39/0.56    inference(cnf_transformation,[],[f37])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (9529)------------------------------
% 1.39/0.56  % (9529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9529)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (9529)Memory used [KB]: 11001
% 1.39/0.56  % (9529)Time elapsed: 0.137 s
% 1.39/0.56  % (9529)------------------------------
% 1.39/0.56  % (9529)------------------------------
% 1.39/0.57  % (9526)Success in time 0.203 s
%------------------------------------------------------------------------------

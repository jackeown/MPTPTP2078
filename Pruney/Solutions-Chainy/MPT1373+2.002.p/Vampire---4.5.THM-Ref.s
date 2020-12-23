%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 694 expanded)
%              Number of leaves         :   15 ( 242 expanded)
%              Depth                    :   28
%              Number of atoms          :  417 (5049 expanded)
%              Number of equality atoms :   40 ( 646 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f136,f177])).

fof(f177,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f175,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f68])).

fof(f68,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ v2_compts_1(sK3,sK1)
      | ~ v2_compts_1(sK2,sK0) )
    & ( v2_compts_1(sK3,sK1)
      | v2_compts_1(sK2,sK0) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK0) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK1)
                | ~ v2_compts_1(X2,sK0) )
              & ( v2_compts_1(X3,sK1)
                | v2_compts_1(X2,sK0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK1)
              | ~ v2_compts_1(X2,sK0) )
            & ( v2_compts_1(X3,sK1)
              | v2_compts_1(X2,sK0) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK1)
            | ~ v2_compts_1(sK2,sK0) )
          & ( v2_compts_1(X3,sK1)
            | v2_compts_1(sK2,sK0) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK1)
          | ~ v2_compts_1(sK2,sK0) )
        & ( v2_compts_1(X3,sK1)
          | v2_compts_1(sK2,sK0) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ~ v2_compts_1(sK3,sK1)
        | ~ v2_compts_1(sK2,sK0) )
      & ( v2_compts_1(sK3,sK1)
        | v2_compts_1(sK2,sK0) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f174,f92])).

fof(f92,plain,(
    r1_tarski(sK2,k2_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | r1_tarski(sK2,k2_struct_0(sK1)) ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,k2_struct_0(sK1)),sK2)
      | r1_tarski(X0,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_struct_0(sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f63,f71])).

fof(f71,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f70,f41])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f67,f42])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f38,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f174,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f55,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_1
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f173,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f172,f145])).

fof(f145,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | spl6_2 ),
    inference(forward_demodulation,[],[f60,f38])).

fof(f60,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_2
  <=> v2_compts_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f172,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ v2_compts_1(sK2,sK0)
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f171,f72])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | v2_compts_1(X0,sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(X0,sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f82,f68])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X0,sK1)
      | ~ v2_compts_1(X0,X1)
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f52,f71])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X4,X1)
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK4(X1,X2),X1)
                    & sK4(X1,X2) = X2
                    & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK4(X1,X2),X1)
        & sK4(X1,X2) = X2
        & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f136,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f134,f34])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f132,f56])).

fof(f56,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f132,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f130,f69])).

% (1388)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_1
    | ~ spl6_2 ),
    inference(superposition,[],[f124,f68])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f123,f92])).

fof(f123,plain,
    ( ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f122,f64])).

fof(f64,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f59,f38])).

fof(f59,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(sK2,sK1)
        | v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_1 ),
    inference(superposition,[],[f48,f107])).

fof(f107,plain,
    ( sK2 = sK4(sK1,sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | spl6_1 ),
    inference(resolution,[],[f95,f92])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k2_struct_0(X0))
        | sK2 = sK4(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) )
    | spl6_1 ),
    inference(subsumption_resolution,[],[f94,f56])).

fof(f94,plain,(
    ! [X0] :
      ( sK2 = sK4(X0,sK2)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | v2_compts_1(sK2,sK0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f81,f69])).

fof(f81,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK4(X5,X4) = X4
      | ~ r1_tarski(X4,k2_struct_0(X5))
      | v2_compts_1(X4,sK0)
      | ~ m1_pre_topc(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK4(X5,X4) = X4
      | ~ r1_tarski(X4,k2_struct_0(X5))
      | v2_compts_1(X4,sK0)
      | ~ m1_pre_topc(X5,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f47,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sK4(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK4(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f39,f58,f54])).

fof(f39,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f40,f58,f54])).

fof(f40,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.52  % (1373)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (1370)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1367)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (1365)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (1371)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (1373)Refutation found. Thanks to Tanya!
% 1.24/0.54  % SZS status Theorem for theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f178,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(avatar_sat_refutation,[],[f61,f62,f136,f177])).
% 1.24/0.54  fof(f177,plain,(
% 1.24/0.54    ~spl6_1 | spl6_2),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f176])).
% 1.24/0.54  fof(f176,plain,(
% 1.24/0.54    $false | (~spl6_1 | spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f175,f69])).
% 1.24/0.54  fof(f69,plain,(
% 1.24/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.24/0.54    inference(backward_demodulation,[],[f36,f68])).
% 1.24/0.54  fof(f68,plain,(
% 1.24/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.24/0.54    inference(resolution,[],[f65,f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f13])).
% 1.24/0.54  fof(f13,plain,(
% 1.24/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.24/0.54  fof(f65,plain,(
% 1.24/0.54    l1_struct_0(sK0)),
% 1.24/0.54    inference(resolution,[],[f34,f42])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.24/0.54  fof(f34,plain,(
% 1.24/0.54    l1_pre_topc(sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    ((((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26,f25,f24,f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f24,plain,(
% 1.24/0.54    ? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f21])).
% 1.24/0.54  fof(f21,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(nnf_transformation,[],[f12])).
% 1.24/0.54  fof(f12,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f11])).
% 1.24/0.54  fof(f11,plain,(
% 1.24/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,negated_conjecture,(
% 1.24/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 1.24/0.54    inference(negated_conjecture,[],[f8])).
% 1.24/0.54  fof(f8,conjecture,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).
% 1.24/0.54  fof(f36,plain,(
% 1.24/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f175,plain,(
% 1.24/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_1 | spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f174,f92])).
% 1.24/0.54  fof(f92,plain,(
% 1.24/0.54    r1_tarski(sK2,k2_struct_0(sK1))),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f91])).
% 1.24/0.54  fof(f91,plain,(
% 1.24/0.54    r1_tarski(sK2,k2_struct_0(sK1)) | r1_tarski(sK2,k2_struct_0(sK1))),
% 1.24/0.54    inference(resolution,[],[f88,f50])).
% 1.24/0.54  fof(f50,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f32])).
% 1.24/0.54  fof(f32,plain,(
% 1.24/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f10])).
% 1.24/0.54  fof(f10,plain,(
% 1.24/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.24/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.54  fof(f88,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(sK5(X0,k2_struct_0(sK1)),sK2) | r1_tarski(X0,k2_struct_0(sK1))) )),
% 1.24/0.54    inference(resolution,[],[f74,f51])).
% 1.24/0.54  fof(f51,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f33])).
% 1.24/0.54  fof(f74,plain,(
% 1.24/0.54    ( ! [X0] : (r2_hidden(X0,k2_struct_0(sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.24/0.54    inference(resolution,[],[f72,f49])).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f19])).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.24/0.54  fof(f72,plain,(
% 1.24/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.24/0.54    inference(backward_demodulation,[],[f63,f71])).
% 1.24/0.54  fof(f71,plain,(
% 1.24/0.54    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.24/0.54    inference(resolution,[],[f70,f41])).
% 1.24/0.54  fof(f70,plain,(
% 1.24/0.54    l1_struct_0(sK1)),
% 1.24/0.54    inference(resolution,[],[f67,f42])).
% 1.24/0.54  fof(f67,plain,(
% 1.24/0.54    l1_pre_topc(sK1)),
% 1.24/0.54    inference(subsumption_resolution,[],[f66,f34])).
% 1.24/0.54  fof(f66,plain,(
% 1.24/0.54    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.24/0.54    inference(resolution,[],[f35,f43])).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.24/0.54  fof(f35,plain,(
% 1.24/0.54    m1_pre_topc(sK1,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f63,plain,(
% 1.24/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.24/0.54    inference(forward_demodulation,[],[f37,f38])).
% 1.24/0.54  fof(f38,plain,(
% 1.24/0.54    sK2 = sK3),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f174,plain,(
% 1.24/0.54    ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl6_1 | spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f173,f55])).
% 1.24/0.54  fof(f55,plain,(
% 1.24/0.54    v2_compts_1(sK2,sK0) | ~spl6_1),
% 1.24/0.54    inference(avatar_component_clause,[],[f54])).
% 1.24/0.54  fof(f54,plain,(
% 1.24/0.54    spl6_1 <=> v2_compts_1(sK2,sK0)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.24/0.54  fof(f173,plain,(
% 1.24/0.54    ~v2_compts_1(sK2,sK0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl6_2),
% 1.24/0.54    inference(subsumption_resolution,[],[f172,f145])).
% 1.24/0.54  fof(f145,plain,(
% 1.24/0.54    ~v2_compts_1(sK2,sK1) | spl6_2),
% 1.24/0.54    inference(forward_demodulation,[],[f60,f38])).
% 1.24/0.54  fof(f60,plain,(
% 1.24/0.54    ~v2_compts_1(sK3,sK1) | spl6_2),
% 1.24/0.54    inference(avatar_component_clause,[],[f58])).
% 1.24/0.54  fof(f58,plain,(
% 1.24/0.54    spl6_2 <=> v2_compts_1(sK3,sK1)),
% 1.24/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.24/0.54  fof(f172,plain,(
% 1.24/0.54    v2_compts_1(sK2,sK1) | ~v2_compts_1(sK2,sK0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.24/0.54    inference(resolution,[],[f171,f72])).
% 1.24/0.54  fof(f171,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | v2_compts_1(X0,sK1) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f170,f34])).
% 1.24/0.54  fof(f170,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK1) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f167,f35])).
% 1.24/0.54  fof(f167,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(X0,sK1) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)) )),
% 1.24/0.54    inference(superposition,[],[f82,f68])).
% 1.24/0.54  fof(f82,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X0,sK1) | ~v2_compts_1(X0,X1) | ~r1_tarski(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 1.24/0.54    inference(superposition,[],[f52,f71])).
% 1.24/0.54  fof(f52,plain,(
% 1.24/0.54    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X4,X1) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(equality_resolution,[],[f45])).
% 1.24/0.54  fof(f45,plain,(
% 1.24/0.54    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f31])).
% 1.24/0.54  fof(f31,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK4(X1,X2),X1) & sK4(X1,X2) = X2 & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK4(X1,X2),X1) & sK4(X1,X2) = X2 & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.24/0.54    introduced(choice_axiom,[])).
% 1.24/0.54  fof(f29,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(rectify,[],[f28])).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(nnf_transformation,[],[f18])).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(flattening,[],[f17])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 1.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 1.24/0.54  fof(f136,plain,(
% 1.24/0.54    spl6_1 | ~spl6_2),
% 1.24/0.54    inference(avatar_contradiction_clause,[],[f135])).
% 1.24/0.54  fof(f135,plain,(
% 1.24/0.54    $false | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f134,f34])).
% 1.24/0.54  fof(f134,plain,(
% 1.24/0.54    ~l1_pre_topc(sK0) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f133,f35])).
% 1.24/0.54  fof(f133,plain,(
% 1.24/0.54    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f132,f56])).
% 1.24/0.54  fof(f56,plain,(
% 1.24/0.54    ~v2_compts_1(sK2,sK0) | spl6_1),
% 1.24/0.54    inference(avatar_component_clause,[],[f54])).
% 1.24/0.54  fof(f132,plain,(
% 1.24/0.54    v2_compts_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f130,f69])).
% 1.24/0.54  % (1388)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.54  fof(f130,plain,(
% 1.24/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(superposition,[],[f124,f68])).
% 1.24/0.54  fof(f124,plain,(
% 1.24/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f123,f92])).
% 1.24/0.54  fof(f123,plain,(
% 1.24/0.54    ( ! [X0] : (v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (spl6_1 | ~spl6_2)),
% 1.24/0.54    inference(subsumption_resolution,[],[f122,f64])).
% 1.24/0.54  fof(f64,plain,(
% 1.24/0.54    v2_compts_1(sK2,sK1) | ~spl6_2),
% 1.24/0.54    inference(forward_demodulation,[],[f59,f38])).
% 1.24/0.54  fof(f59,plain,(
% 1.24/0.54    v2_compts_1(sK3,sK1) | ~spl6_2),
% 1.24/0.54    inference(avatar_component_clause,[],[f58])).
% 1.24/0.54  fof(f122,plain,(
% 1.24/0.54    ( ! [X0] : (~v2_compts_1(sK2,sK1) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl6_1),
% 1.24/0.54    inference(superposition,[],[f48,f107])).
% 1.24/0.54  fof(f107,plain,(
% 1.24/0.54    sK2 = sK4(sK1,sK2) | spl6_1),
% 1.24/0.54    inference(subsumption_resolution,[],[f97,f35])).
% 1.24/0.54  fof(f97,plain,(
% 1.24/0.54    sK2 = sK4(sK1,sK2) | ~m1_pre_topc(sK1,sK0) | spl6_1),
% 1.24/0.54    inference(resolution,[],[f95,f92])).
% 1.24/0.54  fof(f95,plain,(
% 1.24/0.54    ( ! [X0] : (~r1_tarski(sK2,k2_struct_0(X0)) | sK2 = sK4(X0,sK2) | ~m1_pre_topc(X0,sK0)) ) | spl6_1),
% 1.24/0.54    inference(subsumption_resolution,[],[f94,f56])).
% 1.24/0.54  fof(f94,plain,(
% 1.24/0.54    ( ! [X0] : (sK2 = sK4(X0,sK2) | ~r1_tarski(sK2,k2_struct_0(X0)) | v2_compts_1(sK2,sK0) | ~m1_pre_topc(X0,sK0)) )),
% 1.24/0.54    inference(resolution,[],[f81,f69])).
% 1.24/0.54  fof(f81,plain,(
% 1.24/0.54    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | sK4(X5,X4) = X4 | ~r1_tarski(X4,k2_struct_0(X5)) | v2_compts_1(X4,sK0) | ~m1_pre_topc(X5,sK0)) )),
% 1.24/0.54    inference(subsumption_resolution,[],[f78,f34])).
% 1.24/0.54  fof(f78,plain,(
% 1.24/0.54    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | sK4(X5,X4) = X4 | ~r1_tarski(X4,k2_struct_0(X5)) | v2_compts_1(X4,sK0) | ~m1_pre_topc(X5,sK0) | ~l1_pre_topc(sK0)) )),
% 1.24/0.54    inference(superposition,[],[f47,f68])).
% 1.24/0.54  fof(f47,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sK4(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | v2_compts_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f31])).
% 1.24/0.54  fof(f48,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~v2_compts_1(sK4(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f31])).
% 1.24/0.54  fof(f62,plain,(
% 1.24/0.54    spl6_1 | spl6_2),
% 1.24/0.54    inference(avatar_split_clause,[],[f39,f58,f54])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  fof(f61,plain,(
% 1.24/0.54    ~spl6_1 | ~spl6_2),
% 1.24/0.54    inference(avatar_split_clause,[],[f40,f58,f54])).
% 1.24/0.54  fof(f40,plain,(
% 1.24/0.54    ~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)),
% 1.24/0.54    inference(cnf_transformation,[],[f27])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (1373)------------------------------
% 1.24/0.54  % (1373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (1373)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (1373)Memory used [KB]: 10746
% 1.24/0.54  % (1373)Time elapsed: 0.114 s
% 1.24/0.54  % (1373)------------------------------
% 1.24/0.54  % (1373)------------------------------
% 1.24/0.54  % (1368)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.54  % (1363)Success in time 0.174 s
%------------------------------------------------------------------------------

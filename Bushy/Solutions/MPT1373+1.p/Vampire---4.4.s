%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t28_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 458 expanded)
%              Number of leaves         :   17 ( 166 expanded)
%              Depth                    :   24
%              Number of atoms          :  397 (3631 expanded)
%              Number of equality atoms :   39 ( 464 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f112,f326,f365,f368,f392])).

fof(f392,plain,
    ( ~ spl10_0
    | ~ spl10_58 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f390,f101])).

fof(f101,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl10_0
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f390,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f389,f68])).

fof(f68,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ v2_compts_1(sK3,sK1)
      | ~ v2_compts_1(sK2,sK0) )
    & ( v2_compts_1(sK3,sK1)
      | v2_compts_1(sK2,sK0) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53,f52,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,(
    ! [X0] :
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,sK1)
                  | ~ v2_compts_1(X2,X0) )
                & ( v2_compts_1(X3,sK1)
                  | v2_compts_1(X2,X0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_pre_topc(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,X1)
                | ~ v2_compts_1(X2,X0) )
              & ( v2_compts_1(X3,X1)
                | v2_compts_1(X2,X0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ v2_compts_1(X3,X1)
              | ~ v2_compts_1(sK2,X0) )
            & ( v2_compts_1(X3,X1)
              | v2_compts_1(sK2,X0) )
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_compts_1(X3,X1)
            | ~ v2_compts_1(X2,X0) )
          & ( v2_compts_1(X3,X1)
            | v2_compts_1(X2,X0) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ~ v2_compts_1(sK3,X1)
          | ~ v2_compts_1(X2,X0) )
        & ( v2_compts_1(sK3,X1)
          | v2_compts_1(X2,X0) )
        & sK3 = X2
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',t28_compts_1)).

fof(f389,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f387,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f387,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl10_58 ),
    inference(resolution,[],[f364,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v2_compts_1(sK2,X0) )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl10_58
  <=> ! [X0] :
        ( ~ v2_compts_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f368,plain,
    ( spl10_3
    | ~ spl10_50 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f339,f366])).

fof(f366,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f110,f71])).

fof(f71,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_3
  <=> ~ v2_compts_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f339,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl10_50
  <=> v2_compts_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f365,plain,
    ( spl10_58
    | spl10_50 ),
    inference(avatar_split_clause,[],[f361,f338,f363])).

fof(f361,plain,(
    ! [X0] :
      ( v2_compts_1(sK2,sK1)
      | ~ v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f360,f173])).

fof(f173,plain,(
    r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f168,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',t3_subset)).

fof(f168,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f70,f71])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f360,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,u1_struct_0(sK1))
      | v2_compts_1(sK2,sK1)
      | ~ v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f169,f118])).

fof(f118,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f117,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',d3_struct_0)).

fof(f117,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f115,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',dt_l1_pre_topc)).

fof(f115,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f114,f67])).

fof(f114,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',dt_m1_pre_topc)).

fof(f169,plain,(
    ! [X0] :
      ( v2_compts_1(sK2,sK1)
      | ~ v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f168,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X4,X1)
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK4(X1,X2),X1)
        & sK4(X1,X2) = X2
        & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/compts_1__t28_compts_1.p',t11_compts_1)).

fof(f326,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f324,f67])).

fof(f324,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f323,f68])).

fof(f323,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f321,f104])).

fof(f104,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl10_1
  <=> ~ v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f321,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f233,f69])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f232,f173])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,u1_struct_0(sK1))
        | v2_compts_1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f231,f118])).

fof(f231,plain,
    ( ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f230,f119])).

fof(f119,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f107,f71])).

fof(f107,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_2
  <=> v2_compts_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(sK2,sK1)
        | v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f83,f229])).

fof(f229,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f228,f68])).

fof(f228,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f213,f173])).

fof(f213,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | sK2 = sK4(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_1 ),
    inference(superposition,[],[f141,f118])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,k2_struct_0(X2))
        | sK2 = sK4(X2,sK2)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f140,f67])).

fof(f140,plain,
    ( ! [X2] :
        ( sK2 = sK4(X2,sK2)
        | ~ r1_tarski(sK2,k2_struct_0(X2))
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f122,f104])).

fof(f122,plain,(
    ! [X2] :
      ( sK2 = sK4(X2,sK2)
      | ~ r1_tarski(sK2,k2_struct_0(X2))
      | v2_compts_1(sK2,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sK4(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK4(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f112,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f72,f106,f100])).

fof(f72,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f73,f109,f103])).

fof(f73,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------

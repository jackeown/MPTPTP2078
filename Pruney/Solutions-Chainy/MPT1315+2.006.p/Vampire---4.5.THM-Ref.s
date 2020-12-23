%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 827 expanded)
%              Number of leaves         :   24 ( 346 expanded)
%              Depth                    :   21
%              Number of atoms          :  378 (5389 expanded)
%              Number of equality atoms :   75 ( 970 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f161,f185,f197,f225,f228])).

fof(f228,plain,
    ( ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f226,f73])).

fof(f73,plain,(
    ~ v4_pre_topc(sK1,sK2) ),
    inference(forward_demodulation,[],[f47,f46])).

fof(f46,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v4_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v4_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v4_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v4_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f47,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f226,plain,
    ( v4_pre_topc(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f156,f106])).

fof(f106,plain,
    ( sK1 = k2_pre_topc(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_2
  <=> sK1 = k2_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f156,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_9
  <=> v4_pre_topc(k2_pre_topc(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f225,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f223,f43])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f222,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f133,f44])).

fof(f44,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f197,plain,
    ( ~ spl5_2
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl5_2
    | spl5_10 ),
    inference(subsumption_resolution,[],[f193,f87])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f45,f46])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_2
    | spl5_10 ),
    inference(backward_demodulation,[],[f160,f106])).

fof(f160,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_10
  <=> m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f185,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f183,f102])).

fof(f102,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK1),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> r1_tarski(k2_pre_topc(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f183,plain,(
    r1_tarski(k2_pre_topc(sK2,sK1),sK1) ),
    inference(superposition,[],[f179,f149])).

fof(f149,plain,(
    k2_pre_topc(sK2,sK1) = k3_xboole_0(k2_struct_0(sK2),sK1) ),
    inference(superposition,[],[f148,f126])).

fof(f126,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK2),sK1,X4) = k3_xboole_0(X4,sK1) ),
    inference(forward_demodulation,[],[f94,f95])).

fof(f95,plain,(
    ! [X5] : k3_xboole_0(X5,sK1) = k9_subset_1(u1_struct_0(sK2),X5,sK1) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f94,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK2),X4,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X4) ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f148,plain,(
    k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f147,f83])).

fof(f83,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f82,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,(
    k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f146,f41])).

fof(f146,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f145,f43])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(X0,sK1),k2_struct_0(sK2))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f90,f93])).

fof(f93,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK2,X3)
      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f87,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f90,plain,(
    ! [X0] :
      ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(X0,sK1),k2_struct_0(sK2))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f87,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X3),k2_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_pre_topc)).

fof(f179,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1) ),
    inference(forward_demodulation,[],[f178,f172])).

fof(f172,plain,(
    sK1 = k2_xboole_0(sK1,k2_pre_topc(sK2,sK1)) ),
    inference(superposition,[],[f59,f162])).

fof(f162,plain,(
    k2_pre_topc(sK2,sK1) = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    inference(superposition,[],[f149,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (5704)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f178,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(sK1,k2_pre_topc(sK2,sK1))),sK1) ),
    inference(forward_demodulation,[],[f177,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f177,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k2_pre_topc(sK2,sK1))),sK1) ),
    inference(superposition,[],[f63,f172])).

fof(f63,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f161,plain,
    ( spl5_9
    | spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f152,f158,f132,f154])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(sK1,X0)
      | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f151,f93])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_pre_topc(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f67,f148])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f107,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f98,f104,f100])).

fof(f98,plain,
    ( sK1 = k2_pre_topc(sK2,sK1)
    | ~ r1_tarski(k2_pre_topc(sK2,sK1),sK1) ),
    inference(resolution,[],[f96,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f96,plain,(
    r1_tarski(sK1,k2_pre_topc(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f89,f72])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f71,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (5708)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f89,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK2,sK1))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (5720)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:10:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (5718)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (5706)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (5710)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (5698)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (5700)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (5702)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (5712)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (5696)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (5699)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (5701)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (5709)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (5702)Refutation not found, incomplete strategy% (5702)------------------------------
% 0.22/0.52  % (5702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5701)Refutation not found, incomplete strategy% (5701)------------------------------
% 0.22/0.52  % (5701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5701)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5701)Memory used [KB]: 6140
% 0.22/0.52  % (5701)Time elapsed: 0.107 s
% 0.22/0.52  % (5701)------------------------------
% 0.22/0.52  % (5701)------------------------------
% 0.22/0.52  % (5702)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5702)Memory used [KB]: 10618
% 0.22/0.52  % (5702)Time elapsed: 0.074 s
% 0.22/0.52  % (5702)------------------------------
% 0.22/0.52  % (5702)------------------------------
% 1.26/0.52  % (5705)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.26/0.52  % (5717)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.26/0.53  % (5697)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (5715)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.26/0.53  % (5709)Refutation not found, incomplete strategy% (5709)------------------------------
% 1.26/0.53  % (5709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (5709)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (5709)Memory used [KB]: 6140
% 1.26/0.53  % (5709)Time elapsed: 0.116 s
% 1.26/0.53  % (5709)------------------------------
% 1.26/0.53  % (5709)------------------------------
% 1.26/0.53  % (5707)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.54  % (5703)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.54  % (5696)Refutation not found, incomplete strategy% (5696)------------------------------
% 1.26/0.54  % (5696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (5696)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (5696)Memory used [KB]: 10618
% 1.26/0.54  % (5696)Time elapsed: 0.127 s
% 1.26/0.54  % (5696)------------------------------
% 1.26/0.54  % (5696)------------------------------
% 1.26/0.54  % (5697)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % (5716)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.26/0.54  % (5719)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.54  % (5714)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.43/0.54  % SZS output start Proof for theBenchmark
% 1.43/0.55  fof(f229,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(avatar_sat_refutation,[],[f107,f161,f185,f197,f225,f228])).
% 1.43/0.55  fof(f228,plain,(
% 1.43/0.55    ~spl5_2 | ~spl5_9),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f227])).
% 1.43/0.55  fof(f227,plain,(
% 1.43/0.55    $false | (~spl5_2 | ~spl5_9)),
% 1.43/0.55    inference(subsumption_resolution,[],[f226,f73])).
% 1.43/0.55  fof(f73,plain,(
% 1.43/0.55    ~v4_pre_topc(sK1,sK2)),
% 1.43/0.55    inference(forward_demodulation,[],[f47,f46])).
% 1.43/0.55  fof(f46,plain,(
% 1.43/0.55    sK1 = sK3),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f34,plain,(
% 1.43/0.55    (((~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32,f31,f30])).
% 1.43/0.55  fof(f30,plain,(
% 1.43/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f31,plain,(
% 1.43/0.55    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f32,plain,(
% 1.43/0.55    ? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f33,plain,(
% 1.43/0.55    ? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f19,plain,(
% 1.43/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.43/0.55    inference(flattening,[],[f18])).
% 1.43/0.55  fof(f18,plain,(
% 1.43/0.55    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f16])).
% 1.43/0.55  fof(f16,negated_conjecture,(
% 1.43/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 1.43/0.55    inference(negated_conjecture,[],[f15])).
% 1.43/0.55  fof(f15,conjecture,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 1.43/0.55  fof(f47,plain,(
% 1.43/0.55    ~v4_pre_topc(sK3,sK2)),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f226,plain,(
% 1.43/0.55    v4_pre_topc(sK1,sK2) | (~spl5_2 | ~spl5_9)),
% 1.43/0.55    inference(forward_demodulation,[],[f156,f106])).
% 1.43/0.55  fof(f106,plain,(
% 1.43/0.55    sK1 = k2_pre_topc(sK2,sK1) | ~spl5_2),
% 1.43/0.55    inference(avatar_component_clause,[],[f104])).
% 1.43/0.55  fof(f104,plain,(
% 1.43/0.55    spl5_2 <=> sK1 = k2_pre_topc(sK2,sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.55  fof(f156,plain,(
% 1.43/0.55    v4_pre_topc(k2_pre_topc(sK2,sK1),sK2) | ~spl5_9),
% 1.43/0.55    inference(avatar_component_clause,[],[f154])).
% 1.43/0.55  fof(f154,plain,(
% 1.43/0.55    spl5_9 <=> v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.43/0.55  fof(f225,plain,(
% 1.43/0.55    ~spl5_6),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f224])).
% 1.43/0.55  fof(f224,plain,(
% 1.43/0.55    $false | ~spl5_6),
% 1.43/0.55    inference(subsumption_resolution,[],[f223,f43])).
% 1.43/0.55  fof(f43,plain,(
% 1.43/0.55    m1_pre_topc(sK2,sK0)),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f223,plain,(
% 1.43/0.55    ~m1_pre_topc(sK2,sK0) | ~spl5_6),
% 1.43/0.55    inference(subsumption_resolution,[],[f222,f41])).
% 1.43/0.55  fof(f41,plain,(
% 1.43/0.55    l1_pre_topc(sK0)),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f222,plain,(
% 1.43/0.55    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~spl5_6),
% 1.43/0.55    inference(resolution,[],[f133,f44])).
% 1.43/0.55  fof(f44,plain,(
% 1.43/0.55    v4_pre_topc(sK1,sK0)),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f133,plain,(
% 1.43/0.55    ( ! [X0] : (~v4_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | ~spl5_6),
% 1.43/0.55    inference(avatar_component_clause,[],[f132])).
% 1.43/0.55  fof(f132,plain,(
% 1.43/0.55    spl5_6 <=> ! [X0] : (~v4_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.43/0.55  fof(f197,plain,(
% 1.43/0.55    ~spl5_2 | spl5_10),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 1.43/0.55  fof(f196,plain,(
% 1.43/0.55    $false | (~spl5_2 | spl5_10)),
% 1.43/0.55    inference(subsumption_resolution,[],[f193,f87])).
% 1.43/0.55  fof(f87,plain,(
% 1.43/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.43/0.55    inference(forward_demodulation,[],[f45,f46])).
% 1.43/0.55  fof(f45,plain,(
% 1.43/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f193,plain,(
% 1.43/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl5_2 | spl5_10)),
% 1.43/0.55    inference(backward_demodulation,[],[f160,f106])).
% 1.43/0.55  fof(f160,plain,(
% 1.43/0.55    ~m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | spl5_10),
% 1.43/0.55    inference(avatar_component_clause,[],[f158])).
% 1.43/0.55  fof(f158,plain,(
% 1.43/0.55    spl5_10 <=> m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.43/0.55  fof(f185,plain,(
% 1.43/0.55    spl5_1),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f184])).
% 1.43/0.55  fof(f184,plain,(
% 1.43/0.55    $false | spl5_1),
% 1.43/0.55    inference(subsumption_resolution,[],[f183,f102])).
% 1.43/0.55  fof(f102,plain,(
% 1.43/0.55    ~r1_tarski(k2_pre_topc(sK2,sK1),sK1) | spl5_1),
% 1.43/0.55    inference(avatar_component_clause,[],[f100])).
% 1.43/0.55  fof(f100,plain,(
% 1.43/0.55    spl5_1 <=> r1_tarski(k2_pre_topc(sK2,sK1),sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.55  fof(f183,plain,(
% 1.43/0.55    r1_tarski(k2_pre_topc(sK2,sK1),sK1)),
% 1.43/0.55    inference(superposition,[],[f179,f149])).
% 1.43/0.55  fof(f149,plain,(
% 1.43/0.55    k2_pre_topc(sK2,sK1) = k3_xboole_0(k2_struct_0(sK2),sK1)),
% 1.43/0.55    inference(superposition,[],[f148,f126])).
% 1.43/0.55  fof(f126,plain,(
% 1.43/0.55    ( ! [X4] : (k9_subset_1(u1_struct_0(sK2),sK1,X4) = k3_xboole_0(X4,sK1)) )),
% 1.43/0.55    inference(forward_demodulation,[],[f94,f95])).
% 1.43/0.55  fof(f95,plain,(
% 1.43/0.55    ( ! [X5] : (k3_xboole_0(X5,sK1) = k9_subset_1(u1_struct_0(sK2),X5,sK1)) )),
% 1.43/0.55    inference(resolution,[],[f87,f65])).
% 1.43/0.55  fof(f65,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f28])).
% 1.43/0.55  fof(f28,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f8])).
% 1.43/0.55  fof(f8,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.43/0.55  fof(f94,plain,(
% 1.43/0.55    ( ! [X4] : (k9_subset_1(u1_struct_0(sK2),X4,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X4)) )),
% 1.43/0.55    inference(resolution,[],[f87,f66])).
% 1.43/0.55  fof(f66,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f29])).
% 1.43/0.55  fof(f29,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.43/0.55    inference(ennf_transformation,[],[f7])).
% 1.43/0.55  fof(f7,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.43/0.55  fof(f148,plain,(
% 1.43/0.55    k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2))),
% 1.43/0.55    inference(forward_demodulation,[],[f147,f83])).
% 1.43/0.55  fof(f83,plain,(
% 1.43/0.55    sK1 = k2_pre_topc(sK0,sK1)),
% 1.43/0.55    inference(subsumption_resolution,[],[f82,f41])).
% 1.43/0.55  fof(f82,plain,(
% 1.43/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.43/0.55    inference(subsumption_resolution,[],[f74,f44])).
% 1.43/0.55  fof(f74,plain,(
% 1.43/0.55    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.43/0.55    inference(resolution,[],[f42,f57])).
% 1.43/0.55  fof(f57,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f27])).
% 1.43/0.55  fof(f27,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(flattening,[],[f26])).
% 1.43/0.55  fof(f26,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f17])).
% 1.43/0.55  fof(f17,plain,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.43/0.55    inference(pure_predicate_removal,[],[f14])).
% 1.43/0.55  fof(f14,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.43/0.55  fof(f42,plain,(
% 1.43/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.55    inference(cnf_transformation,[],[f34])).
% 1.43/0.55  fof(f147,plain,(
% 1.43/0.55    k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2))),
% 1.43/0.55    inference(subsumption_resolution,[],[f146,f41])).
% 1.43/0.55  fof(f146,plain,(
% 1.43/0.55    k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2)) | ~l1_pre_topc(sK0)),
% 1.43/0.55    inference(resolution,[],[f145,f43])).
% 1.43/0.55  fof(f145,plain,(
% 1.43/0.55    ( ! [X0] : (~m1_pre_topc(sK2,X0) | k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(X0,sK1),k2_struct_0(sK2)) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(subsumption_resolution,[],[f90,f93])).
% 1.43/0.55  fof(f93,plain,(
% 1.43/0.55    ( ! [X3] : (~m1_pre_topc(sK2,X3) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 1.43/0.55    inference(resolution,[],[f87,f50])).
% 1.43/0.55  fof(f50,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f21])).
% 1.43/0.55  fof(f21,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f10])).
% 1.43/0.55  fof(f10,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.43/0.55  fof(f90,plain,(
% 1.43/0.55    ( ! [X0] : (k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(X0,sK1),k2_struct_0(sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(resolution,[],[f87,f68])).
% 1.43/0.55  fof(f68,plain,(
% 1.43/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X3),k2_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(equality_resolution,[],[f55])).
% 1.43/0.55  fof(f55,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f24])).
% 1.43/0.55  fof(f24,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(flattening,[],[f23])).
% 1.43/0.55  fof(f23,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f12])).
% 1.43/0.55  fof(f12,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)))))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_pre_topc)).
% 1.43/0.55  fof(f179,plain,(
% 1.43/0.55    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK1),sK1)) )),
% 1.43/0.55    inference(forward_demodulation,[],[f178,f172])).
% 1.43/0.55  fof(f172,plain,(
% 1.43/0.55    sK1 = k2_xboole_0(sK1,k2_pre_topc(sK2,sK1))),
% 1.43/0.55    inference(superposition,[],[f59,f162])).
% 1.43/0.55  fof(f162,plain,(
% 1.43/0.55    k2_pre_topc(sK2,sK1) = k3_xboole_0(sK1,k2_struct_0(sK2))),
% 1.43/0.55    inference(superposition,[],[f149,f58])).
% 1.43/0.55  fof(f58,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f1])).
% 1.43/0.55  fof(f1,axiom,(
% 1.43/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.55  % (5704)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.43/0.55  fof(f59,plain,(
% 1.43/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.43/0.55    inference(cnf_transformation,[],[f3])).
% 1.43/0.55  fof(f3,axiom,(
% 1.43/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.43/0.55  fof(f178,plain,(
% 1.43/0.55    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(sK1,k2_pre_topc(sK2,sK1))),sK1)) )),
% 1.43/0.55    inference(forward_demodulation,[],[f177,f64])).
% 1.43/0.55  fof(f64,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f4])).
% 1.43/0.55  fof(f4,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.43/0.55  fof(f177,plain,(
% 1.43/0.55    ( ! [X0] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k2_pre_topc(sK2,sK1))),sK1)) )),
% 1.43/0.55    inference(superposition,[],[f63,f172])).
% 1.43/0.55  fof(f63,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f6])).
% 1.43/0.55  fof(f6,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.43/0.55  fof(f161,plain,(
% 1.43/0.55    spl5_9 | spl5_6 | ~spl5_10),
% 1.43/0.55    inference(avatar_split_clause,[],[f152,f158,f132,f154])).
% 1.43/0.55  fof(f152,plain,(
% 1.43/0.55    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(sK1,X0) | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(subsumption_resolution,[],[f151,f93])).
% 1.43/0.55  fof(f151,plain,(
% 1.43/0.55    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_pre_topc(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(superposition,[],[f67,f148])).
% 1.43/0.55  fof(f67,plain,(
% 1.43/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(equality_resolution,[],[f54])).
% 1.43/0.55  fof(f54,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f38])).
% 1.43/0.55  fof(f38,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.43/0.55  fof(f37,plain,(
% 1.43/0.55    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.43/0.55    introduced(choice_axiom,[])).
% 1.43/0.55  fof(f36,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(rectify,[],[f35])).
% 1.43/0.55  fof(f35,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(nnf_transformation,[],[f22])).
% 1.43/0.55  fof(f22,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f11])).
% 1.43/0.55  fof(f11,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 1.43/0.55  fof(f107,plain,(
% 1.43/0.55    ~spl5_1 | spl5_2),
% 1.43/0.55    inference(avatar_split_clause,[],[f98,f104,f100])).
% 1.43/0.55  fof(f98,plain,(
% 1.43/0.55    sK1 = k2_pre_topc(sK2,sK1) | ~r1_tarski(k2_pre_topc(sK2,sK1),sK1)),
% 1.43/0.55    inference(resolution,[],[f96,f62])).
% 1.43/0.55  fof(f62,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f40])).
% 1.43/0.55  fof(f40,plain,(
% 1.43/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.55    inference(flattening,[],[f39])).
% 1.43/0.55  fof(f39,plain,(
% 1.43/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.55    inference(nnf_transformation,[],[f2])).
% 1.43/0.55  fof(f2,axiom,(
% 1.43/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.55  fof(f96,plain,(
% 1.43/0.55    r1_tarski(sK1,k2_pre_topc(sK2,sK1))),
% 1.43/0.55    inference(subsumption_resolution,[],[f89,f72])).
% 1.43/0.55  fof(f72,plain,(
% 1.43/0.55    l1_pre_topc(sK2)),
% 1.43/0.55    inference(subsumption_resolution,[],[f71,f41])).
% 1.43/0.55  fof(f71,plain,(
% 1.43/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.43/0.55    inference(resolution,[],[f43,f49])).
% 1.43/0.55  fof(f49,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f20])).
% 1.43/0.55  fof(f20,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f9])).
% 1.43/0.55  % (5708)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.43/0.55  fof(f9,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.43/0.55  fof(f89,plain,(
% 1.43/0.55    r1_tarski(sK1,k2_pre_topc(sK2,sK1)) | ~l1_pre_topc(sK2)),
% 1.43/0.55    inference(resolution,[],[f87,f56])).
% 1.43/0.55  fof(f56,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f25])).
% 1.43/0.55  fof(f25,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f13])).
% 1.43/0.55  % (5720)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.43/0.55  fof(f13,axiom,(
% 1.43/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.43/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.43/0.55  % SZS output end Proof for theBenchmark
% 1.43/0.55  % (5697)------------------------------
% 1.43/0.55  % (5697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (5697)Termination reason: Refutation
% 1.43/0.55  
% 1.43/0.55  % (5697)Memory used [KB]: 10746
% 1.43/0.55  % (5697)Time elapsed: 0.103 s
% 1.43/0.55  % (5697)------------------------------
% 1.43/0.55  % (5697)------------------------------
% 1.43/0.56  % (5693)Success in time 0.189 s
%------------------------------------------------------------------------------

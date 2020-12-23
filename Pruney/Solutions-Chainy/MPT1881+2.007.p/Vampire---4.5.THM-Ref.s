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
% DateTime   : Thu Dec  3 13:21:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 (1071 expanded)
%              Number of leaves         :   15 ( 301 expanded)
%              Depth                    :   26
%              Number of atoms          :  355 (7203 expanded)
%              Number of equality atoms :   50 ( 239 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(resolution,[],[f464,f83])).

fof(f83,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f464,plain,(
    v1_subset_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f293,f463])).

fof(f463,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f95,f462])).

fof(f462,plain,(
    sP0(sK3,sK2) ),
    inference(global_subsumption,[],[f181,f457])).

fof(f457,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f454])).

fof(f454,plain,
    ( sK3 != sK3
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(superposition,[],[f71,f444])).

fof(f444,plain,(
    sK3 = sK4(sK3,sK2) ),
    inference(resolution,[],[f440,f83])).

fof(f440,plain,
    ( v1_subset_1(sK3,sK3)
    | sK3 = sK4(sK3,sK2) ),
    inference(backward_demodulation,[],[f395,f439])).

fof(f439,plain,(
    sK3 = k2_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f434,f83])).

fof(f434,plain,
    ( v1_subset_1(sK3,sK3)
    | sK3 = k2_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f359,f293])).

fof(f359,plain,
    ( v3_tex_2(sK3,sK2)
    | sK3 = k2_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(forward_demodulation,[],[f320,f290])).

fof(f290,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(global_subsumption,[],[f108,f286])).

fof(f286,plain,
    ( u1_struct_0(sK2) = sK3
    | ~ v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f283,f96])).

fof(f96,plain,
    ( sP0(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f94,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK2))
          | ~ v3_tex_2(X1,sK2) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
          | v3_tex_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( v1_subset_1(sK3,u1_struct_0(sK2))
        | ~ v3_tex_2(sK3,sK2) )
      & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
        | v3_tex_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f283,plain,
    ( ~ sP0(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f279,f87])).

fof(f87,plain,(
    r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f279,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | u1_struct_0(sK2) = X0
      | ~ sP0(X0,sK2) ) ),
    inference(resolution,[],[f262,f178])).

fof(f178,plain,(
    v2_tex_2(u1_struct_0(sK2),sK2) ),
    inference(resolution,[],[f177,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tex_2(X0,sK2) ) ),
    inference(global_subsumption,[],[f53,f52,f50,f174])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v1_tdlat_3(sK2)
      | v2_tex_2(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f50,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | u1_struct_0(X1) = X0
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f67,f84])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | X0 = X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f108,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f107,f55])).

fof(f55,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f107,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | u1_struct_0(sK2) = sK3 ),
    inference(resolution,[],[f78,f54])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f320,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2)) ),
    inference(backward_demodulation,[],[f183,f290])).

fof(f183,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK2)
    | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f157,f178])).

fof(f157,plain,
    ( ~ v2_tex_2(u1_struct_0(sK2),sK2)
    | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2))
    | v3_tex_2(u1_struct_0(sK2),sK2) ),
    inference(resolution,[],[f129,f97])).

fof(f97,plain,
    ( ~ sP0(u1_struct_0(sK2),sK2)
    | v3_tex_2(u1_struct_0(sK2),sK2) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
    sP1(sK2,u1_struct_0(sK2)) ),
    inference(resolution,[],[f91,f84])).

fof(f129,plain,(
    ! [X2,X3] :
      ( sP0(X2,X3)
      | ~ v2_tex_2(X2,X3)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X3),sK4(X2,X3)) ) ),
    inference(forward_demodulation,[],[f128,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,X3)
      | sP0(X2,X3)
      | u1_struct_0(X3) = k2_xboole_0(sK4(X2,X3),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f123,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f123,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK4(X4,X5),u1_struct_0(X5))
      | ~ v2_tex_2(X4,X5)
      | sP0(X4,X5) ) ),
    inference(resolution,[],[f68,f80])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f395,plain,
    ( v1_subset_1(sK3,sK3)
    | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f293,f189])).

fof(f189,plain,
    ( v3_tex_2(sK3,sK2)
    | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f153,f181])).

fof(f153,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f111,f95])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sK4(X0,X1) = k2_xboole_0(X0,sK4(X0,X1)) ) ),
    inference(resolution,[],[f70,f76])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f181,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f177,f54])).

fof(f95,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f94,f65])).

fof(f293,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,sK3) ),
    inference(backward_demodulation,[],[f56,f290])).

fof(f56,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (18433)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (18441)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (18433)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f464,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f57,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    v1_subset_1(sK3,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f463])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f95,f462])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    sP0(sK3,sK2)),
% 0.21/0.50    inference(global_subsumption,[],[f181,f457])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f454])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    sK3 != sK3 | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(superposition,[],[f71,f444])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    sK3 = sK4(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f440,f83])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    v1_subset_1(sK3,sK3) | sK3 = sK4(sK3,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f395,f439])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    sK3 = k2_xboole_0(sK3,sK4(sK3,sK2))),
% 0.21/0.50    inference(resolution,[],[f434,f83])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    v1_subset_1(sK3,sK3) | sK3 = k2_xboole_0(sK3,sK4(sK3,sK2))),
% 0.21/0.50    inference(resolution,[],[f359,f293])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    v3_tex_2(sK3,sK2) | sK3 = k2_xboole_0(sK3,sK4(sK3,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f320,f290])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    u1_struct_0(sK2) = sK3),
% 0.21/0.50    inference(global_subsumption,[],[f108,f286])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    u1_struct_0(sK2) = sK3 | ~v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f283,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    sP0(sK3,sK2) | ~v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f94,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    sP1(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f91,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f39,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f72,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(definition_folding,[],[f24,f34,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~sP0(sK3,sK2) | u1_struct_0(sK2) = sK3),
% 0.21/0.50    inference(resolution,[],[f279,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    r1_tarski(sK3,u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f80,f54])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | u1_struct_0(sK2) = X0 | ~sP0(X0,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f262,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    v2_tex_2(u1_struct_0(sK2),sK2)),
% 0.21/0.50    inference(resolution,[],[f177,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f59,f58])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tex_2(X0,sK2)) )),
% 0.21/0.50    inference(global_subsumption,[],[f53,f52,f50,f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v1_tdlat_3(sK2) | v2_tex_2(X0,sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f73,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v2_pre_topc(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v1_tdlat_3(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_tex_2(u1_struct_0(X1),X1) | ~r1_tarski(X0,u1_struct_0(X1)) | u1_struct_0(X1) = X0 | ~sP0(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f67,f84])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | X0 = X3 | ~sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.50    inference(flattening,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = sK3),
% 0.21/0.50    inference(resolution,[],[f107,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    v1_subset_1(sK3,u1_struct_0(sK2)) | u1_struct_0(sK2) = sK3),
% 0.21/0.50    inference(resolution,[],[f78,f54])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f183,f290])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    v3_tex_2(u1_struct_0(sK2),sK2) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f178])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v2_tex_2(u1_struct_0(sK2),sK2) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK2),sK4(u1_struct_0(sK2),sK2)) | v3_tex_2(u1_struct_0(sK2),sK2)),
% 0.21/0.50    inference(resolution,[],[f129,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ~sP0(u1_struct_0(sK2),sK2) | v3_tex_2(u1_struct_0(sK2),sK2)),
% 0.21/0.50    inference(resolution,[],[f92,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    sP1(sK2,u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f91,f84])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X2,X3] : (sP0(X2,X3) | ~v2_tex_2(X2,X3) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X3),sK4(X2,X3))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v2_tex_2(X2,X3) | sP0(X2,X3) | u1_struct_0(X3) = k2_xboole_0(sK4(X2,X3),u1_struct_0(X3))) )),
% 0.21/0.50    inference(resolution,[],[f123,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r1_tarski(sK4(X4,X5),u1_struct_0(X5)) | ~v2_tex_2(X4,X5) | sP0(X4,X5)) )),
% 0.21/0.50    inference(resolution,[],[f68,f80])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    v1_subset_1(sK3,sK3) | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2))),
% 0.21/0.50    inference(resolution,[],[f293,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    v3_tex_2(sK3,sK2) | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f153,f181])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ~v2_tex_2(sK3,sK2) | sK4(sK3,sK2) = k2_xboole_0(sK3,sK4(sK3,sK2)) | v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f111,f95])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP0(X0,X1) | ~v2_tex_2(X0,X1) | sK4(X0,X1) = k2_xboole_0(X0,sK4(X0,X1))) )),
% 0.21/0.50    inference(resolution,[],[f70,f76])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f177,f54])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f94,f65])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ~v3_tex_2(sK3,sK2) | v1_subset_1(sK3,sK3)),
% 0.21/0.51    inference(backward_demodulation,[],[f56,f290])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (18433)------------------------------
% 0.21/0.51  % (18433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18433)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (18433)Memory used [KB]: 6524
% 0.21/0.51  % (18433)Time elapsed: 0.068 s
% 0.21/0.51  % (18433)------------------------------
% 0.21/0.51  % (18433)------------------------------
% 0.21/0.51  % (18420)Success in time 0.148 s
%------------------------------------------------------------------------------

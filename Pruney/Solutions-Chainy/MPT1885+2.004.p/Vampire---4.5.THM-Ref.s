%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 849 expanded)
%              Number of leaves         :   11 ( 273 expanded)
%              Depth                    :   27
%              Number of atoms          :  388 (7581 expanded)
%              Number of equality atoms :   34 ( 704 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f181,f41])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK5
        | ~ v4_tex_2(X2,sK4)
        | ~ m1_pre_topc(X2,sK4)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v3_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,sK4)
              | ~ m1_pre_topc(X2,sK4)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ v4_tex_2(X2,sK4)
            | ~ m1_pre_topc(X2,sK4)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v3_tex_2(X1,sK4)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK5
          | ~ v4_tex_2(X2,sK4)
          | ~ m1_pre_topc(X2,sK4)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v3_tex_2(sK5,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f181,plain,(
    ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f180,f109])).

fof(f109,plain,(
    sK5 = u1_struct_0(sK7(sK5,sK4)) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK7(X0,X1)) = X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK7(X0,X1)) = X0
        & m1_pre_topc(sK7(X0,X1),X1)
        & v1_pre_topc(sK7(X0,X1))
        & ~ v2_struct_0(sK7(X0,X1)) )
      | ~ sP3(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK7(X0,X1)) = X0
        & m1_pre_topc(sK7(X0,X1),X1)
        & v1_pre_topc(sK7(X0,X1))
        & ~ v2_struct_0(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f102,plain,(
    sP3(sK5,sK4) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,
    ( sP3(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f100,f38])).

fof(f38,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,
    ( sP3(sK5,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f39,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,
    ( sP3(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,
    ( sP3(sK5,sK4)
    | v1_xboole_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f95,f41])).

fof(f95,plain,
    ( sP3(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f19])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f92,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f91,plain,(
    sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f42,plain,(
    v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,
    ( sP1(sK4,sK5)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v3_tex_2(X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f86,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f17,f16,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f180,plain,(
    ~ m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f179,f91])).

fof(f179,plain,
    ( ~ sP1(sK4,sK5)
    | ~ m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f178,f109])).

fof(f178,plain,
    ( ~ sP1(sK4,u1_struct_0(sK7(sK5,sK4)))
    | ~ m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f175,f108])).

fof(f108,plain,(
    m1_pre_topc(sK7(sK5,sK4),sK4) ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK7(X0,X1),X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f175,plain,
    ( ~ sP1(sK4,u1_struct_0(sK7(sK5,sK4)))
    | ~ m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_pre_topc(sK7(sK5,sK4),sK4) ),
    inference(resolution,[],[f174,f143])).

fof(f143,plain,(
    ! [X1] :
      ( v4_tex_2(X1,sK4)
      | ~ sP1(sK4,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_pre_topc(X1,sK4) ) ),
    inference(subsumption_resolution,[],[f142,f37])).

fof(f142,plain,(
    ! [X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(sK4,u1_struct_0(X1))
      | v4_tex_2(X1,sK4)
      | ~ m1_pre_topc(X1,sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f141,f39])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(sK4,u1_struct_0(X1))
      | v4_tex_2(X1,sK4)
      | ~ m1_pre_topc(X1,sK4)
      | ~ l1_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(sK4,u1_struct_0(X1))
      | v4_tex_2(X1,sK4)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_pre_topc(X1,sK4)
      | ~ l1_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f135,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).

fof(f135,plain,(
    ! [X1] :
      ( v3_tex_2(X1,sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(sK4,X1) ) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X0,X1)
      | ~ sP1(X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X3] :
      ( sP2(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(resolution,[],[f39,f54])).

fof(f174,plain,(
    ~ v4_tex_2(sK7(sK5,sK4),sK4) ),
    inference(subsumption_resolution,[],[f173,f109])).

fof(f173,plain,
    ( ~ v4_tex_2(sK7(sK5,sK4),sK4)
    | sK5 != u1_struct_0(sK7(sK5,sK4)) ),
    inference(subsumption_resolution,[],[f114,f108])).

fof(f114,plain,
    ( ~ v4_tex_2(sK7(sK5,sK4),sK4)
    | ~ m1_pre_topc(sK7(sK5,sK4),sK4)
    | sK5 != u1_struct_0(sK7(sK5,sK4)) ),
    inference(subsumption_resolution,[],[f113,f106])).

fof(f106,plain,(
    ~ v2_struct_0(sK7(sK5,sK4)) ),
    inference(resolution,[],[f102,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK7(X0,X1))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,
    ( ~ v4_tex_2(sK7(sK5,sK4),sK4)
    | ~ m1_pre_topc(sK7(sK5,sK4),sK4)
    | sK5 != u1_struct_0(sK7(sK5,sK4))
    | v2_struct_0(sK7(sK5,sK4)) ),
    inference(resolution,[],[f107,f43])).

fof(f43,plain,(
    ! [X2] :
      ( ~ v1_pre_topc(X2)
      | ~ v4_tex_2(X2,sK4)
      | ~ m1_pre_topc(X2,sK4)
      | u1_struct_0(X2) != sK5
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    v1_pre_topc(sK7(sK5,sK4)) ),
    inference(resolution,[],[f102,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK7(X0,X1))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (18772)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.47  % (18770)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (18770)Refutation not found, incomplete strategy% (18770)------------------------------
% 0.20/0.48  % (18770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18770)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18770)Memory used [KB]: 10490
% 0.20/0.48  % (18770)Time elapsed: 0.004 s
% 0.20/0.48  % (18770)------------------------------
% 0.20/0.48  % (18770)------------------------------
% 0.20/0.48  % (18779)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.48  % (18779)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f181,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    (! [X2] : (u1_struct_0(X2) != sK5 | ~v4_tex_2(X2,sK4) | ~m1_pre_topc(X2,sK4) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f8,f22,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK4) | ~m1_pre_topc(X2,sK4) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK4) | ~m1_pre_topc(X2,sK4) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) => (! [X2] : (u1_struct_0(X2) != sK5 | ~v4_tex_2(X2,sK4) | ~m1_pre_topc(X2,sK4) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.48    inference(forward_demodulation,[],[f180,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    sK5 = u1_struct_0(sK7(sK5,sK4))),
% 0.20/0.48    inference(resolution,[],[f102,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (u1_struct_0(sK7(X0,X1)) = X0 | ~sP3(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : ((u1_struct_0(sK7(X0,X1)) = X0 & m1_pre_topc(sK7(X0,X1),X1) & v1_pre_topc(sK7(X0,X1)) & ~v2_struct_0(sK7(X0,X1))) | ~sP3(X0,X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK7(X0,X1)) = X0 & m1_pre_topc(sK7(X0,X1),X1) & v1_pre_topc(sK7(X0,X1)) & ~v2_struct_0(sK7(X0,X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP3(X0,X1))),
% 0.20/0.48    inference(rectify,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP3(X1,X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP3(X1,X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    sP3(sK5,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~v2_struct_0(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    sP3(sK5,sK4) | v2_struct_0(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f100,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v2_pre_topc(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    sP3(sK5,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f99,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    l1_pre_topc(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    sP3(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~v1_xboole_0(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    sP3(sK5,sK4) | v1_xboole_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f41])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    sP3(sK5,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) | v1_xboole_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)),
% 0.20/0.48    inference(resolution,[],[f92,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP3(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (sP3(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(definition_folding,[],[f12,f19])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    v2_tex_2(sK5,sK4)),
% 0.20/0.48    inference(resolution,[],[f91,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~sP1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    sP1(sK4,sK5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v3_tex_2(sK5,sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    sP1(sK4,sK5) | ~v3_tex_2(sK5,sK4)),
% 0.20/0.48    inference(resolution,[],[f86,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP1(X1,X0) | ~v3_tex_2(X0,X1) | ~sP2(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.20/0.48    inference(rectify,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    sP2(sK5,sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f39])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.20/0.48    inference(resolution,[],[f41,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f10,f17,f16,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f179,f91])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ~sP1(sK4,sK5) | ~m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.49    inference(forward_demodulation,[],[f178,f109])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ~sP1(sK4,u1_struct_0(sK7(sK5,sK4))) | ~m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f175,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    m1_pre_topc(sK7(sK5,sK4),sK4)),
% 0.20/0.49    inference(resolution,[],[f102,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_pre_topc(sK7(X0,X1),X1) | ~sP3(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~sP1(sK4,u1_struct_0(sK7(sK5,sK4))) | ~m1_subset_1(u1_struct_0(sK7(sK5,sK4)),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_pre_topc(sK7(sK5,sK4),sK4)),
% 0.20/0.49    inference(resolution,[],[f174,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X1] : (v4_tex_2(X1,sK4) | ~sP1(sK4,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_pre_topc(X1,sK4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f142,f37])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(sK4,u1_struct_0(X1)) | v4_tex_2(X1,sK4) | ~m1_pre_topc(X1,sK4) | v2_struct_0(sK4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f39])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(sK4,u1_struct_0(X1)) | v4_tex_2(X1,sK4) | ~m1_pre_topc(X1,sK4) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(sK4,u1_struct_0(X1)) | v4_tex_2(X1,sK4) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_pre_topc(X1,sK4) | ~l1_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 0.20/0.49    inference(resolution,[],[f135,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tex_2(X2,X0) | ~v4_tex_2(X1,X0)) & (v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tex_2)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X1] : (v3_tex_2(X1,sK4) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(sK4,X1)) )),
% 0.20/0.49    inference(resolution,[],[f72,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v3_tex_2(X0,X1) | ~sP1(X1,X0) | ~sP2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X3] : (sP2(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.20/0.49    inference(resolution,[],[f39,f54])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~v4_tex_2(sK7(sK5,sK4),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f173,f109])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~v4_tex_2(sK7(sK5,sK4),sK4) | sK5 != u1_struct_0(sK7(sK5,sK4))),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f108])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~v4_tex_2(sK7(sK5,sK4),sK4) | ~m1_pre_topc(sK7(sK5,sK4),sK4) | sK5 != u1_struct_0(sK7(sK5,sK4))),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f106])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ~v2_struct_0(sK7(sK5,sK4))),
% 0.20/0.49    inference(resolution,[],[f102,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_struct_0(sK7(X0,X1)) | ~sP3(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~v4_tex_2(sK7(sK5,sK4),sK4) | ~m1_pre_topc(sK7(sK5,sK4),sK4) | sK5 != u1_struct_0(sK7(sK5,sK4)) | v2_struct_0(sK7(sK5,sK4))),
% 0.20/0.49    inference(resolution,[],[f107,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2] : (~v1_pre_topc(X2) | ~v4_tex_2(X2,sK4) | ~m1_pre_topc(X2,sK4) | u1_struct_0(X2) != sK5 | v2_struct_0(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    v1_pre_topc(sK7(sK5,sK4))),
% 0.20/0.49    inference(resolution,[],[f102,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_pre_topc(sK7(X0,X1)) | ~sP3(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (18779)------------------------------
% 0.20/0.49  % (18779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18779)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18779)Memory used [KB]: 1663
% 0.20/0.49  % (18779)Time elapsed: 0.078 s
% 0.20/0.49  % (18779)------------------------------
% 0.20/0.49  % (18779)------------------------------
% 0.20/0.49  % (18766)Success in time 0.131 s
%------------------------------------------------------------------------------

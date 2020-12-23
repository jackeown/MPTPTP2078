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
% DateTime   : Thu Dec  3 13:21:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 288 expanded)
%              Number of leaves         :   15 (  87 expanded)
%              Depth                    :   30
%              Number of atoms          :  502 (1814 expanded)
%              Number of equality atoms :   61 ( 129 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(subsumption_resolution,[],[f277,f90])).

fof(f90,plain,(
    ~ sP0(sK6,sK5) ),
    inference(subsumption_resolution,[],[f89,f49])).

fof(f49,plain,(
    v2_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_tex_2(sK6,sK5)
    & v2_tex_2(sK6,sK5)
    & v1_tops_1(sK6,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK5)
          & v2_tex_2(X1,sK5)
          & v1_tops_1(X1,sK5)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK5)
        & v2_tex_2(X1,sK5)
        & v1_tops_1(X1,sK5)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ~ v3_tex_2(sK6,sK5)
      & v2_tex_2(sK6,sK5)
      & v1_tops_1(sK6,sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f89,plain,
    ( ~ sP0(sK6,sK5)
    | ~ v2_tex_2(sK6,sK5) ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,(
    ~ sP1(sK5,sK6) ),
    inference(subsumption_resolution,[],[f86,f50])).

fof(f50,plain,(
    ~ v3_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,
    ( ~ sP1(sK5,sK6)
    | v3_tex_2(sK6,sK5) ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f85,plain,(
    sP2(sK6,sK5) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f46,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,
    ( sP2(sK6,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f277,plain,(
    sP0(sK6,sK5) ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,
    ( sK6 != sK6
    | sP0(sK6,sK5) ),
    inference(superposition,[],[f60,f248])).

fof(f248,plain,(
    sK6 = sK7(sK6,sK5) ),
    inference(subsumption_resolution,[],[f247,f90])).

fof(f247,plain,
    ( sP0(sK6,sK5)
    | sK6 = sK7(sK6,sK5) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,
    ( sP0(sK6,sK5)
    | sK6 = sK7(sK6,sK5)
    | sP0(sK6,sK5) ),
    inference(resolution,[],[f241,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK7(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK7(X0,X1) != X0
          & r1_tarski(X0,sK7(X0,X1))
          & v2_tex_2(sK7(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK7(X0,X1) != X0
        & r1_tarski(X0,sK7(X0,X1))
        & v2_tex_2(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,sK7(X0,sK5))
      | sP0(X0,sK5)
      | sK6 = sK7(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f240,f46])).

fof(f240,plain,(
    ! [X0] :
      ( sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ l1_pre_topc(sK5) ) ),
    inference(subsumption_resolution,[],[f239,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f239,plain,(
    ! [X0] :
      ( sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(subsumption_resolution,[],[f238,f45])).

fof(f45,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f238,plain,(
    ! [X0] :
      ( sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | sP0(X0,sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(resolution,[],[f236,f107])).

fof(f107,plain,(
    ! [X2,X3] :
      ( sP3(X2,sK7(X3,X2))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | sP0(X3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f106,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK7(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | sP0(X3,X2)
      | ~ v2_tex_2(sK7(X3,X2),X2)
      | sP3(X2,sK7(X3,X2)) ) ),
    inference(resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP3(X1,X0) )
        & ( sP3(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP4(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP3(X0,X1) )
        & ( sP3(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP4(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP3(X0,X1) )
      | ~ sP4(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sP4(sK7(X0,X1),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f236,plain,(
    ! [X0] :
      ( ~ sP3(sK5,sK7(X0,sK5))
      | sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5)) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK6,sK7(X0,sK5))
      | sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ sP3(sK5,sK7(X0,sK5)) ) ),
    inference(resolution,[],[f233,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK7(X0,sK5),X1)
      | ~ r1_tarski(sK6,X1)
      | sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ sP3(sK5,X1) ) ),
    inference(subsumption_resolution,[],[f230,f48])).

fof(f48,plain,(
    v1_tops_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK7(X0,sK5),X1)
      | ~ r1_tarski(sK6,X1)
      | sK6 = sK7(X0,sK5)
      | sP0(X0,sK5)
      | ~ v1_tops_1(sK6,sK5)
      | ~ r1_tarski(sK6,sK7(X0,sK5))
      | ~ sP3(sK5,X1) ) ),
    inference(resolution,[],[f224,f47])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r1_tarski(sK7(X1,sK5),X0)
      | ~ r1_tarski(sK6,X0)
      | sK6 = sK7(X1,sK5)
      | sP0(X1,sK5)
      | ~ v1_tops_1(X2,sK5)
      | ~ r1_tarski(X2,sK7(X1,sK5))
      | ~ sP3(sK5,X0) ) ),
    inference(subsumption_resolution,[],[f223,f46])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(sK5,X0)
      | ~ r1_tarski(sK7(X1,sK5),X0)
      | ~ r1_tarski(sK6,X0)
      | sK6 = sK7(X1,sK5)
      | sP0(X1,sK5)
      | ~ v1_tops_1(X2,sK5)
      | ~ r1_tarski(X2,sK7(X1,sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ l1_pre_topc(sK5) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(sK5,X0)
      | ~ r1_tarski(sK7(X1,sK5),X0)
      | ~ r1_tarski(sK6,X0)
      | sK6 = sK7(X1,sK5)
      | sP0(X1,sK5)
      | ~ v1_tops_1(X2,sK5)
      | ~ r1_tarski(X2,sK7(X1,sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ l1_pre_topc(sK5)
      | sP0(X1,sK5) ) ),
    inference(resolution,[],[f219,f146])).

fof(f146,plain,(
    ! [X2,X3,X1] :
      ( v1_tops_1(sK7(X2,X3),X3)
      | ~ v1_tops_1(X1,X3)
      | ~ r1_tarski(X1,sK7(X2,X3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | sP0(X2,X3) ) ),
    inference(resolution,[],[f64,f57])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | v1_tops_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

fof(f219,plain,(
    ! [X2,X1] :
      ( ~ v1_tops_1(sK7(X1,sK5),sK5)
      | ~ sP3(sK5,X2)
      | ~ r1_tarski(sK7(X1,sK5),X2)
      | ~ r1_tarski(sK6,X2)
      | sK6 = sK7(X1,sK5)
      | sP0(X1,sK5) ) ),
    inference(resolution,[],[f217,f57])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | sK6 = X1
      | ~ sP3(sK5,X0)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(sK6,X0)
      | ~ v1_tops_1(X1,sK5) ) ),
    inference(subsumption_resolution,[],[f216,f46])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6,X0)
      | sK6 = X1
      | ~ sP3(sK5,X0)
      | ~ l1_pre_topc(sK5)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v1_tops_1(X1,sK5) ) ),
    inference(subsumption_resolution,[],[f213,f48])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6,X0)
      | sK6 = X1
      | ~ sP3(sK5,X0)
      | ~ v1_tops_1(sK6,sK5)
      | ~ l1_pre_topc(sK5)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v1_tops_1(X1,sK5) ) ),
    inference(resolution,[],[f155,f47])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | X2 = X3
      | ~ sP3(X0,X1)
      | ~ v1_tops_1(X3,X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1)
      | ~ v1_tops_1(X3,X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1)
      | ~ v1_tops_1(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f138,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X2,u1_struct_0(X0)) = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X2,u1_struct_0(X0)) = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f67,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( sK8(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK8(X0,X1)))
          & r1_tarski(sK8(X0,X1),X1)
          & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK8(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK8(X0,X1)))
        & r1_tarski(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (10683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (10702)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (10694)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (10693)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (10685)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (10701)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (10686)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (10693)Refutation not found, incomplete strategy% (10693)------------------------------
% 0.22/0.51  % (10693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10696)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (10683)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (10698)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (10692)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (10704)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (10684)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (10693)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10693)Memory used [KB]: 6268
% 0.22/0.52  % (10693)Time elapsed: 0.087 s
% 0.22/0.52  % (10693)------------------------------
% 0.22/0.52  % (10693)------------------------------
% 0.22/0.52  % (10678)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (10689)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (10699)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (10678)Refutation not found, incomplete strategy% (10678)------------------------------
% 0.22/0.52  % (10678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10678)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10678)Memory used [KB]: 10618
% 0.22/0.52  % (10678)Time elapsed: 0.105 s
% 0.22/0.52  % (10678)------------------------------
% 0.22/0.52  % (10678)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f277,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~sP0(sK6,sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v2_tex_2(sK6,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    (~v3_tex_2(sK6,sK5) & v2_tex_2(sK6,sK5) & v1_tops_1(sK6,sK5) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f25,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK5) & v2_tex_2(X1,sK5) & v1_tops_1(X1,sK5) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X1] : (~v3_tex_2(X1,sK5) & v2_tex_2(X1,sK5) & v1_tops_1(X1,sK5) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) => (~v3_tex_2(sK6,sK5) & v2_tex_2(sK6,sK5) & v1_tops_1(sK6,sK5) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~sP0(sK6,sK5) | ~v2_tex_2(sK6,sK5)),
% 0.22/0.53    inference(resolution,[],[f88,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~sP1(sK5,sK6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f86,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ~v3_tex_2(sK6,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~sP1(sK5,sK6) | v3_tex_2(sK6,sK5)),
% 0.22/0.53    inference(resolution,[],[f85,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.22/0.53    inference(rectify,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    sP2(sK6,sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f83,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    l1_pre_topc(sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    sP2(sK6,sK5) | ~l1_pre_topc(sK5)),
% 0.22/0.53    inference(resolution,[],[f61,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(definition_folding,[],[f11,f19,f18,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    sP0(sK6,sK5)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f257])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    sK6 != sK6 | sP0(sK6,sK5)),
% 0.22/0.53    inference(superposition,[],[f60,f248])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    sK6 = sK7(sK6,sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f90])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    sP0(sK6,sK5) | sK6 = sK7(sK6,sK5)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f246])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    sP0(sK6,sK5) | sK6 = sK7(sK6,sK5) | sP0(sK6,sK5)),
% 0.22/0.53    inference(resolution,[],[f241,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,sK7(X0,X1)) | sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | (sK7(X0,X1) != X0 & r1_tarski(X0,sK7(X0,X1)) & v2_tex_2(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK7(X0,X1) != X0 & r1_tarski(X0,sK7(X0,X1)) & v2_tex_2(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK6,sK7(X0,sK5)) | sP0(X0,sK5) | sK6 = sK7(X0,sK5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f240,f46])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    ( ! [X0] : (sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~l1_pre_topc(sK5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f239,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~v2_struct_0(sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ( ! [X0] : (sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | v2_struct_0(sK5) | ~l1_pre_topc(sK5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f238,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    v2_pre_topc(sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ( ! [X0] : (sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK5)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f237])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    ( ! [X0] : (sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | sP0(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 0.22/0.53    inference(resolution,[],[f236,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X2,X3] : (sP3(X2,sK7(X3,X2)) | ~v2_pre_topc(X2) | v2_struct_0(X2) | sP0(X3,X2) | ~l1_pre_topc(X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f106,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_tex_2(sK7(X0,X1),X1) | sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | sP0(X3,X2) | ~v2_tex_2(sK7(X3,X2),X2) | sP3(X2,sK7(X3,X2))) )),
% 0.22/0.53    inference(resolution,[],[f95,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP4(X0,X1) | ~v2_tex_2(X0,X1) | sP3(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP3(X1,X0)) & (sP3(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP4(X0,X1))),
% 0.22/0.53    inference(rectify,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP3(X0,X1)) & (sP3(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP4(X1,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP3(X0,X1)) | ~sP4(X1,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP4(sK7(X0,X1),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP0(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f71,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP4(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (sP4(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(definition_folding,[],[f16,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X0] : (~sP3(sK5,sK7(X0,sK5)) | sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK6,sK7(X0,sK5)) | sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~sP3(sK5,sK7(X0,sK5))) )),
% 0.22/0.53    inference(resolution,[],[f233,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK7(X0,sK5),X1) | ~r1_tarski(sK6,X1) | sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~sP3(sK5,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f230,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v1_tops_1(sK6,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK7(X0,sK5),X1) | ~r1_tarski(sK6,X1) | sK6 = sK7(X0,sK5) | sP0(X0,sK5) | ~v1_tops_1(sK6,sK5) | ~r1_tarski(sK6,sK7(X0,sK5)) | ~sP3(sK5,X1)) )),
% 0.22/0.53    inference(resolution,[],[f224,f47])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~r1_tarski(sK7(X1,sK5),X0) | ~r1_tarski(sK6,X0) | sK6 = sK7(X1,sK5) | sP0(X1,sK5) | ~v1_tops_1(X2,sK5) | ~r1_tarski(X2,sK7(X1,sK5)) | ~sP3(sK5,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f223,f46])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP3(sK5,X0) | ~r1_tarski(sK7(X1,sK5),X0) | ~r1_tarski(sK6,X0) | sK6 = sK7(X1,sK5) | sP0(X1,sK5) | ~v1_tops_1(X2,sK5) | ~r1_tarski(X2,sK7(X1,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f222])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP3(sK5,X0) | ~r1_tarski(sK7(X1,sK5),X0) | ~r1_tarski(sK6,X0) | sK6 = sK7(X1,sK5) | sP0(X1,sK5) | ~v1_tops_1(X2,sK5) | ~r1_tarski(X2,sK7(X1,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | sP0(X1,sK5)) )),
% 0.22/0.53    inference(resolution,[],[f219,f146])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (v1_tops_1(sK7(X2,X3),X3) | ~v1_tops_1(X1,X3) | ~r1_tarski(X1,sK7(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | sP0(X2,X3)) )),
% 0.22/0.53    inference(resolution,[],[f64,f57])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | v1_tops_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~v1_tops_1(sK7(X1,sK5),sK5) | ~sP3(sK5,X2) | ~r1_tarski(sK7(X1,sK5),X2) | ~r1_tarski(sK6,X2) | sK6 = sK7(X1,sK5) | sP0(X1,sK5)) )),
% 0.22/0.53    inference(resolution,[],[f217,f57])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | sK6 = X1 | ~sP3(sK5,X0) | ~r1_tarski(X1,X0) | ~r1_tarski(sK6,X0) | ~v1_tops_1(X1,sK5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f216,f46])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK6,X0) | sK6 = X1 | ~sP3(sK5,X0) | ~l1_pre_topc(sK5) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_tops_1(X1,sK5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f213,f48])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(sK6,X0) | sK6 = X1 | ~sP3(sK5,X0) | ~v1_tops_1(sK6,sK5) | ~l1_pre_topc(sK5) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_tops_1(X1,sK5)) )),
% 0.22/0.53    inference(resolution,[],[f155,f47])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | X2 = X3 | ~sP3(X0,X1) | ~v1_tops_1(X3,X0) | ~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X2,X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f152])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1) | ~v1_tops_1(X3,X0) | ~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1) | ~v1_tops_1(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(superposition,[],[f138,f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X2,u1_struct_0(X0)) = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X2) | ~v1_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X0),X2,u1_struct_0(X0)) = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(superposition,[],[f67,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP3(X0,X1) | (sK8(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK8(X0,X1))) & r1_tarski(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK8(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK8(X0,X1))) & r1_tarski(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK7(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10683)------------------------------
% 0.22/0.53  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10683)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10683)Memory used [KB]: 6268
% 0.22/0.53  % (10683)Time elapsed: 0.091 s
% 0.22/0.53  % (10683)------------------------------
% 0.22/0.53  % (10683)------------------------------
% 0.22/0.53  % (10677)Success in time 0.164 s
%------------------------------------------------------------------------------

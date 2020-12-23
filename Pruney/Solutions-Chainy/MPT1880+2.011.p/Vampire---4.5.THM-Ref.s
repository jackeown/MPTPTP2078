%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 506 expanded)
%              Number of leaves         :   16 ( 157 expanded)
%              Depth                    :   21
%              Number of atoms          :  456 (3365 expanded)
%              Number of equality atoms :   70 ( 220 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(global_subsumption,[],[f46,f80,f488])).

fof(f488,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f485])).

fof(f485,plain,
    ( sK3 != sK3
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(superposition,[],[f56,f356])).

fof(f356,plain,(
    sK3 = sK4(sK3,sK2) ),
    inference(global_subsumption,[],[f46,f80,f355])).

fof(f355,plain,
    ( sK3 = sK4(sK3,sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(forward_demodulation,[],[f354,f332])).

fof(f332,plain,(
    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) ),
    inference(global_subsumption,[],[f46,f80,f331])).

fof(f331,plain,
    ( sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f328,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

% (8085)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f328,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,sK4(X1,sK2))
      | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),u1_struct_0(sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(forward_demodulation,[],[f325,f100])).

fof(f100,plain,(
    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) ),
    inference(global_subsumption,[],[f45,f98])).

fof(f98,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f94,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).

fof(f27,plain,
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
          ( ~ v3_tex_2(X1,sK2)
          & v2_tex_2(X1,sK2)
          & v1_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ v3_tex_2(X1,sK2)
        & v2_tex_2(X1,sK2)
        & v1_tops_1(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v3_tex_2(sK3,sK2)
      & v2_tex_2(sK3,sK2)
      & v1_tops_1(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_tops_1(X0,sK2)
      | u1_struct_0(sK2) = k2_pre_topc(sK2,X0) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f45,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f325,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,sK4(X1,sK2))
      | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,sK3))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(resolution,[],[f323,f44])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4(X1,sK2))
      | k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,X0)) = X0
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X0,sK4(X1,sK2))
      | k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,X0)) = X0
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(resolution,[],[f299,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f299,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(sK4(X3,sK2),sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X2,sK4(X3,sK2))
      | k9_subset_1(u1_struct_0(sK2),sK4(X3,sK2),k2_pre_topc(sK2,X2)) = X2
      | sP0(X3,sK2)
      | ~ v2_tex_2(X3,sK2) ) ),
    inference(resolution,[],[f296,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X1,sK2)
      | ~ r1_tarski(X0,X1)
      | k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,X0)) = X0 ) ),
    inference(global_subsumption,[],[f43,f41,f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,X0)) = X0
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
                & r1_tarski(sK5(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1)))
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f354,plain,
    ( sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(forward_demodulation,[],[f353,f179])).

fof(f179,plain,(
    u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2)) ),
    inference(global_subsumption,[],[f46,f80,f178])).

fof(f178,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f151,f55])).

fof(f151,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,sK4(X1,sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X1,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,sK4(X1,sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X1,sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(resolution,[],[f148,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_tops_1(sK4(X0,sK2),sK2)
      | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X0,sK2))
      | sP0(X0,sK2)
      | ~ v2_tex_2(X0,sK2) ) ),
    inference(resolution,[],[f94,f53])).

fof(f148,plain,(
    ! [X1] :
      ( v1_tops_1(sK4(X1,sK2),sK2)
      | ~ r1_tarski(sK3,sK4(X1,sK2))
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(global_subsumption,[],[f45,f146])).

fof(f146,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK3,sK4(X1,sK2))
      | ~ v1_tops_1(sK3,sK2)
      | v1_tops_1(sK4(X1,sK2),sK2)
      | sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2) ) ),
    inference(resolution,[],[f139,f44])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r1_tarski(X2,sK4(X3,sK2))
      | ~ v1_tops_1(X2,sK2)
      | v1_tops_1(sK4(X3,sK2),sK2)
      | sP0(X3,sK2)
      | ~ v2_tex_2(X3,sK2) ) ),
    inference(resolution,[],[f136,f53])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_tops_1(X0,sK2)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_tops_1(X1,sK2) ) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f353,plain,
    ( sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),k2_pre_topc(sK2,sK4(sK3,sK2)))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),k2_pre_topc(sK2,sK4(sK3,sK2)))
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[],[f326,f127])).

fof(f127,plain,(
    r1_tarski(sK4(sK3,sK2),sK4(sK3,sK2)) ),
    inference(superposition,[],[f65,f125])).

fof(f125,plain,(
    sK4(sK3,sK2) = k3_xboole_0(sK4(sK3,sK2),sK4(sK3,sK2)) ),
    inference(superposition,[],[f124,f72])).

fof(f72,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X1) = X1 ),
    inference(subsumption_resolution,[],[f69,f70])).

fof(f70,plain,(
    ! [X0] : sP6(X0) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f68_D])).

fof(f68_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f66,f68_D])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f124,plain,(
    ! [X6] : k9_subset_1(u1_struct_0(sK2),X6,sK4(sK3,sK2)) = k3_xboole_0(X6,sK4(sK3,sK2)) ),
    inference(global_subsumption,[],[f46,f122])).

fof(f122,plain,(
    ! [X6] :
      ( ~ v2_tex_2(sK3,sK2)
      | k9_subset_1(u1_struct_0(sK2),X6,sK4(sK3,sK2)) = k3_xboole_0(X6,sK4(sK3,sK2)) ) ),
    inference(resolution,[],[f92,f80])).

fof(f92,plain,(
    ! [X2,X3,X1] :
      ( sP0(X1,X2)
      | ~ v2_tex_2(X1,X2)
      | k9_subset_1(u1_struct_0(X2),X3,sK4(X1,X2)) = k3_xboole_0(X3,sK4(X1,X2)) ) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f326,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK4(X2,sK2),sK4(X3,sK2))
      | sK4(X2,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(X3,sK2),k2_pre_topc(sK2,sK4(X2,sK2)))
      | sP0(X3,sK2)
      | ~ v2_tex_2(X3,sK2)
      | sP0(X2,sK2)
      | ~ v2_tex_2(X2,sK2) ) ),
    inference(resolution,[],[f323,f53])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ~ sP0(sK3,sK2) ),
    inference(global_subsumption,[],[f47,f78])).

fof(f78,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f75,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f73,f44])).

fof(f73,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f47,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.19/0.34  % Computer   : n005.cluster.edu
% 0.19/0.34  % Model      : x86_64 x86_64
% 0.19/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.19/0.34  % Memory     : 8042.1875MB
% 0.19/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 12:57:02 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.44  % (8093)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.45  % (8100)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (8093)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (8081)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f46,f80,f488])).
% 0.21/0.49  fof(f488,plain,(
% 0.21/0.49    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f485])).
% 0.21/0.49  fof(f485,plain,(
% 0.21/0.49    sK3 != sK3 | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.49    inference(superposition,[],[f56,f356])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    sK3 = sK4(sK3,sK2)),
% 0.21/0.49    inference(global_subsumption,[],[f46,f80,f355])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    sK3 = sK4(sK3,sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f354,f332])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2))),
% 0.21/0.49    inference(global_subsumption,[],[f46,f80,f331])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f330])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    sK3 = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.49    inference(resolution,[],[f328,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f32])).
% 0.21/0.49  % (8085)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(sK3,sK4(X1,sK2)) | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),u1_struct_0(sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f325,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)),
% 0.21/0.49    inference(global_subsumption,[],[f45,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v1_tops_1(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f94,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f28,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_tops_1(X0,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f58,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    l1_pre_topc(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_tops_1(sK3,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(sK3,sK4(X1,sK2)) | sK3 = k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,sK3)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f323,f44])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4(X1,sK2)) | k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,X0)) = X0 | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f322])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK4(X1,sK2)) | k9_subset_1(u1_struct_0(sK2),sK4(X1,sK2),k2_pre_topc(sK2,X0)) = X0 | sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f299,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v2_tex_2(sK4(X3,sK2),sK2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X2,sK4(X3,sK2)) | k9_subset_1(u1_struct_0(sK2),sK4(X3,sK2),k2_pre_topc(sK2,X2)) = X2 | sP0(X3,sK2) | ~v2_tex_2(X3,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f296,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X1,sK2) | ~r1_tarski(X0,X1) | k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,X0)) = X0) )),
% 0.21/0.49    inference(global_subsumption,[],[f43,f41,f295])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,X0)) = X0 | v2_struct_0(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f61,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    v2_pre_topc(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK5(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK5(X0,X1))) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),u1_struct_0(sK2)) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f353,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2))),
% 0.21/0.50    inference(global_subsumption,[],[f46,f80,f178])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(sK3,sK2)) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f151,f55])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK3,sK4(X1,sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X1,sK2))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK3,sK4(X1,sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X1,sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f148,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_tops_1(sK4(X0,sK2),sK2) | u1_struct_0(sK2) = k2_pre_topc(sK2,sK4(X0,sK2)) | sP0(X0,sK2) | ~v2_tex_2(X0,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f94,f53])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X1] : (v1_tops_1(sK4(X1,sK2),sK2) | ~r1_tarski(sK3,sK4(X1,sK2)) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.50    inference(global_subsumption,[],[f45,f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(sK3,sK4(X1,sK2)) | ~v1_tops_1(sK3,sK2) | v1_tops_1(sK4(X1,sK2),sK2) | sP0(X1,sK2) | ~v2_tex_2(X1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f139,f44])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X2,sK4(X3,sK2)) | ~v1_tops_1(X2,sK2) | v1_tops_1(sK4(X3,sK2),sK2) | sP0(X3,sK2) | ~v2_tex_2(X3,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f136,f53])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_tops_1(X0,sK2) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v1_tops_1(X1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f60,f43])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),k2_pre_topc(sK2,sK4(sK3,sK2))) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f350])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    sK4(sK3,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK3,sK2),k2_pre_topc(sK2,sK4(sK3,sK2))) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f326,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    r1_tarski(sK4(sK3,sK2),sK4(sK3,sK2))),
% 0.21/0.50    inference(superposition,[],[f65,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sK4(sK3,sK2) = k3_xboole_0(sK4(sK3,sK2),sK4(sK3,sK2))),
% 0.21/0.50    inference(superposition,[],[f124,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f69,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (sP6(X0)) )),
% 0.21/0.50    inference(resolution,[],[f68,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP6(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f68_D])).
% 0.21/0.50  fof(f68_D,plain,(
% 0.21/0.50    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP6(X0)) )),
% 0.21/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~sP6(X0)) )),
% 0.21/0.50    inference(general_splitting,[],[f66,f68_D])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X6] : (k9_subset_1(u1_struct_0(sK2),X6,sK4(sK3,sK2)) = k3_xboole_0(X6,sK4(sK3,sK2))) )),
% 0.21/0.50    inference(global_subsumption,[],[f46,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X6] : (~v2_tex_2(sK3,sK2) | k9_subset_1(u1_struct_0(sK2),X6,sK4(sK3,sK2)) = k3_xboole_0(X6,sK4(sK3,sK2))) )),
% 0.21/0.50    inference(resolution,[],[f92,f80])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (sP0(X1,X2) | ~v2_tex_2(X1,X2) | k9_subset_1(u1_struct_0(X2),X3,sK4(X1,X2)) = k3_xboole_0(X3,sK4(X1,X2))) )),
% 0.21/0.50    inference(resolution,[],[f53,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_tarski(sK4(X2,sK2),sK4(X3,sK2)) | sK4(X2,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(X3,sK2),k2_pre_topc(sK2,sK4(X2,sK2))) | sP0(X3,sK2) | ~v2_tex_2(X3,sK2) | sP0(X2,sK2) | ~v2_tex_2(X2,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f323,f53])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~sP0(sK3,sK2)),
% 0.21/0.50    inference(global_subsumption,[],[f47,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(resolution,[],[f75,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    sP1(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f73,f44])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f57,f43])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(definition_folding,[],[f16,f25,f24])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~v3_tex_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v2_tex_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8093)------------------------------
% 0.21/0.50  % (8093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8093)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8093)Memory used [KB]: 6780
% 0.21/0.50  % (8093)Time elapsed: 0.079 s
% 0.21/0.50  % (8093)------------------------------
% 0.21/0.50  % (8093)------------------------------
% 0.21/0.50  % (8102)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (8080)Success in time 0.144 s
%------------------------------------------------------------------------------

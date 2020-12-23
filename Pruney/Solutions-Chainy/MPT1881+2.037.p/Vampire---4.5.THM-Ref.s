%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 541 expanded)
%              Number of leaves         :   17 ( 144 expanded)
%              Depth                    :   17
%              Number of atoms          :  527 (3407 expanded)
%              Number of equality atoms :   50 ( 161 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f117,f124,f220,f226,f307,f344,f527,f561,f647])).

fof(f647,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_4
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_4
    | ~ spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f645,f581])).

fof(f581,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f580,f127])).

fof(f127,plain,
    ( u1_struct_0(sK0) = sK1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f126,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f126,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(resolution,[],[f63,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f63,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f580,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f579,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f579,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f393,f539])).

fof(f539,plain,
    ( v2_tex_2(sK1,sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f78,f127])).

fof(f78,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_4
  <=> v2_tex_2(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f393,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f211,f60])).

fof(f60,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f211,plain,
    ( v3_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
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
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
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
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f645,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_8
    | spl3_9 ),
    inference(resolution,[],[f644,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f644,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f640,f123])).

fof(f123,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_9
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f640,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f116,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_8
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f561,plain,
    ( spl3_2
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | spl3_2
    | spl3_12 ),
    inference(subsumption_resolution,[],[f179,f127])).

fof(f179,plain,
    ( u1_struct_0(sK0) != sK1
    | spl3_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_12
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f527,plain,
    ( spl3_5
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f98,f495])).

fof(f495,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f494,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f494,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f493,f33])).

fof(f493,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f492,f32])).

fof(f32,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f492,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f443,f187])).

fof(f187,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f34,f180])).

fof(f180,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f443,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(superposition,[],[f53,f180])).

fof(f53,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f98,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f344,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f329,f312])).

fof(f312,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f64,f310])).

fof(f310,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f309,f73])).

% (4995)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f73,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f309,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f299,f78])).

fof(f299,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1 ),
    inference(resolution,[],[f152,f167])).

fof(f167,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f34,f47])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | sK1 = X0
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f151,f33])).

fof(f151,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f150,f34])).

fof(f150,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f329,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f279,f310])).

fof(f279,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f307,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_12 ),
    inference(subsumption_resolution,[],[f305,f73])).

fof(f305,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_4
    | spl3_12 ),
    inference(subsumption_resolution,[],[f304,f78])).

fof(f304,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_12 ),
    inference(subsumption_resolution,[],[f299,f179])).

fof(f226,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f225,f76,f72])).

fof(f225,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f224,f31])).

fof(f224,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f80,f33])).

fof(f80,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f32,f53])).

fof(f220,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f218,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f218,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_3 ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f124,plain,
    ( ~ spl3_5
    | ~ spl3_9
    | spl3_1 ),
    inference(avatar_split_clause,[],[f119,f58,f121,f96])).

fof(f119,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f118,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f92,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f60,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,
    ( ~ spl3_5
    | spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f112,f58,f114,f96])).

fof(f112,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f111,f33])).

% (4996)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f111,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f91,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62,f58])).

fof(f35,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f36,f62,f58])).

fof(f36,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (4986)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (4986)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4994)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.48  % (4980)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f648,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f65,f66,f117,f124,f220,f226,f307,f344,f527,f561,f647])).
% 0.21/0.49  fof(f647,plain,(
% 0.21/0.49    spl3_1 | spl3_2 | ~spl3_4 | ~spl3_8 | spl3_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f646])).
% 0.21/0.49  fof(f646,plain,(
% 0.21/0.49    $false | (spl3_1 | spl3_2 | ~spl3_4 | ~spl3_8 | spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f645,f581])).
% 0.21/0.49  fof(f581,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f580,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | spl3_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 0.21/0.49    inference(resolution,[],[f63,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f579,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f579,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f393,f539])).
% 0.21/0.49  fof(f539,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | (spl3_2 | ~spl3_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f78,f127])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    v2_tex_2(u1_struct_0(sK0),sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_4 <=> v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~v3_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f34,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.49  fof(f645,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl3_8 | spl3_9)),
% 0.21/0.49    inference(resolution,[],[f644,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f644,plain,(
% 0.21/0.49    ~r1_tarski(sK2(sK0,sK1),sK1) | (~spl3_8 | spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f640,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    sK1 != sK2(sK0,sK1) | spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl3_9 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f640,plain,(
% 0.21/0.49    sK1 = sK2(sK0,sK1) | ~r1_tarski(sK2(sK0,sK1),sK1) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f116,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl3_8 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    spl3_2 | spl3_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f560])).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    $false | (spl3_2 | spl3_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f127])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    u1_struct_0(sK0) != sK1 | spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl3_12 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f527,plain,(
% 0.21/0.49    spl3_5 | ~spl3_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.49  fof(f526,plain,(
% 0.21/0.49    $false | (spl3_5 | ~spl3_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f495])).
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~spl3_12),
% 0.21/0.49    inference(subsumption_resolution,[],[f494,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f494,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.21/0.49    inference(subsumption_resolution,[],[f493,f33])).
% 0.21/0.49  fof(f493,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.21/0.49    inference(subsumption_resolution,[],[f492,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v1_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f492,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.21/0.49    inference(subsumption_resolution,[],[f443,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_12),
% 0.21/0.49    inference(backward_demodulation,[],[f34,f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_12),
% 0.21/0.49    inference(superposition,[],[f53,f180])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_5 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f343])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f329,f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    v1_subset_1(sK1,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f64,f310])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f309,f73])).
% 0.21/0.49  % (4995)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f78])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    u1_struct_0(sK0) = sK1 | ~v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f152,f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f34,f47])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | sK1 = X0 | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f151,f33])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f150,f34])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f59,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 0.21/0.49    inference(backward_demodulation,[],[f279,f310])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f73,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f306])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f305,f73])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_4 | spl3_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f304,f78])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f179])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ~spl3_3 | spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f225,f76,f72])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f31])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f33])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f32,f53])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f219])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    $false | spl3_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_3),
% 0.21/0.49    inference(resolution,[],[f74,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~spl3_5 | ~spl3_9 | spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f119,f58,f121,f96])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f33])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f34])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f60,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~spl3_5 | spl3_8 | spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f58,f114,f96])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f33])).
% 0.21/0.49  % (4996)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f34])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f60,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f62,f58])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f62,f58])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4986)------------------------------
% 0.21/0.49  % (4986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4986)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4986)Memory used [KB]: 10874
% 0.21/0.49  % (4986)Time elapsed: 0.063 s
% 0.21/0.49  % (4986)------------------------------
% 0.21/0.49  % (4986)------------------------------
% 0.21/0.49  % (4988)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (4974)Success in time 0.139 s
%------------------------------------------------------------------------------

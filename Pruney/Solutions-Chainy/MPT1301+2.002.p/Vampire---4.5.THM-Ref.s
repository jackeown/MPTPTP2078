%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 389 expanded)
%              Number of leaves         :   18 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 (2012 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30880)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f169,f232,f237,f272,f277,f285])).

fof(f285,plain,
    ( ~ spl6_8
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f283,f33])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_tops_2(sK3,sK2)
    & v2_tops_2(sK4,sK2)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(X1,X0)
                & v2_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,sK2)
              & v2_tops_2(X2,sK2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(X1,sK2)
            & v2_tops_2(X2,sK2)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(sK3,sK2)
          & v2_tops_2(X2,sK2)
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(sK3,sK2)
        & v2_tops_2(X2,sK2)
        & r1_tarski(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v2_tops_2(sK3,sK2)
      & v2_tops_2(sK4,sK2)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

% (30879)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v2_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f280,f35])).

fof(f35,plain,(
    v2_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f280,plain,
    ( ~ v2_tops_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(resolution,[],[f278,f75])).

fof(f75,plain,(
    ! [X0] :
      ( sP0(sK2,X0)
      | ~ v2_tops_2(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tops_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v2_tops_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tops_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( ( v2_tops_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tops_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( v2_tops_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0] :
      ( sP1(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f17,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v4_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f278,plain,
    ( ~ sP0(sK2,sK4)
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(resolution,[],[f271,f242])).

fof(f242,plain,
    ( r2_hidden(sK5(sK2,sK4),sK4)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f240,f144])).

fof(f144,plain,
    ( r2_hidden(sK5(sK2,sK3),sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_8
  <=> r2_hidden(sK5(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f240,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,sK3),X2)
        | r2_hidden(sK5(sK2,X2),X2) )
    | ~ spl6_12 ),
    inference(resolution,[],[f231,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v4_pre_topc(sK5(X0,X1),X0)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v4_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v4_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ sP0(sK2,X0)
        | ~ r2_hidden(sK5(sK2,sK3),X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK3),X0)
        | ~ sP0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK4),X0)
        | ~ sP0(sK2,X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK4),X0)
        | ~ sP0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f277,plain,
    ( ~ spl6_8
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f274,f144])).

fof(f274,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK4)
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(resolution,[],[f273,f231])).

fof(f273,plain,
    ( sP0(sK2,sK4)
    | ~ spl6_13 ),
    inference(resolution,[],[f268,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f268,plain,
    ( v4_pre_topc(sK5(sK2,sK4),sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_13
  <=> v4_pre_topc(sK5(sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f272,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f248,f230,f142,f270,f266])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK4),X0)
        | v4_pre_topc(sK5(sK2,sK4),sK2)
        | ~ sP0(sK2,X0) )
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f244,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v4_pre_topc(X3,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f244,plain,
    ( m1_subset_1(sK5(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f242,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f237,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f235,f36])).

fof(f36,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f235,plain,
    ( v2_tops_2(sK3,sK2)
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f234,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f234,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_tops_2(sK3,sK2)
    | ~ spl6_11 ),
    inference(resolution,[],[f233,f76])).

fof(f76,plain,(
    ! [X1] :
      ( ~ sP0(sK2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | v2_tops_2(X1,sK2) ) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tops_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f233,plain,
    ( sP0(sK2,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f228,f42])).

fof(f228,plain,
    ( v4_pre_topc(sK5(sK2,sK3),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl6_11
  <=> v4_pre_topc(sK5(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f232,plain,
    ( spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f162,f230,f226])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK2,sK3),X0)
      | v4_pre_topc(sK5(sK2,sK3),sK2)
      | ~ sP0(sK2,X0) ) ),
    inference(resolution,[],[f157,f39])).

fof(f157,plain,(
    m1_subset_1(sK5(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f57,f115])).

fof(f115,plain,(
    r2_hidden(sK5(sK2,sK3),sK3) ),
    inference(subsumption_resolution,[],[f114,f32])).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r2_hidden(sK5(sK2,sK3),sK3) ),
    inference(resolution,[],[f112,f36])).

fof(f112,plain,(
    ! [X2] :
      ( v2_tops_2(X2,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | r2_hidden(sK5(sK2,X2),X2) ) ),
    inference(resolution,[],[f76,f41])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f32,f50])).

fof(f169,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl6_7 ),
    inference(resolution,[],[f167,f115])).

fof(f167,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl6_7 ),
    inference(resolution,[],[f147,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK4)) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f34,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_7 ),
    inference(resolution,[],[f140,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f140,plain,
    ( v1_xboole_0(sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_7
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f145,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f121,f142,f138])).

fof(f121,plain,
    ( r2_hidden(sK5(sK2,sK3),sK4)
    | v1_xboole_0(sK4) ),
    inference(resolution,[],[f120,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f120,plain,(
    m1_subset_1(sK5(sK2,sK3),sK4) ),
    inference(resolution,[],[f54,f115])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | m1_subset_1(X0,sK4) ) ),
    inference(resolution,[],[f53,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:46:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (30875)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.48  % (30874)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (30875)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (30876)WARNING: option uwaf not known.
% 0.21/0.49  % (30867)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.49  % (30868)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (30886)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (30866)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (30872)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.50  % (30870)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (30877)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.50  % (30881)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (30880)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f145,f169,f232,f237,f272,f277,f285])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ~spl6_8 | ~spl6_12 | ~spl6_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    $false | (~spl6_8 | ~spl6_12 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ((~v2_tops_2(sK3,sK2) & v2_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f21,f20,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(X1,sK2) & v2_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (~v2_tops_2(X1,sK2) & v2_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (? [X2] : (~v2_tops_2(sK3,sK2) & v2_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X2] : (~v2_tops_2(sK3,sK2) & v2_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v2_tops_2(sK3,sK2) & v2_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  % (30879)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(X1,X0) & (v2_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | (~spl6_8 | ~spl6_12 | ~spl6_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v2_tops_2(sK4,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~v2_tops_2(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | (~spl6_8 | ~spl6_12 | ~spl6_14)),
% 0.21/0.50    inference(resolution,[],[f278,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (sP0(sK2,X0) | ~v2_tops_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.21/0.50    inference(resolution,[],[f52,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tops_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (((v2_tops_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tops_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.50    inference(rectify,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X1,X0] : (((v2_tops_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tops_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X1,X0] : ((v2_tops_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.21/0.50    inference(resolution,[],[f31,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(definition_folding,[],[f11,f17,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~sP0(sK2,sK4) | (~spl6_8 | ~spl6_12 | ~spl6_14)),
% 0.21/0.50    inference(resolution,[],[f271,f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK4),sK4) | (~spl6_8 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f240,f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),sK4) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl6_8 <=> r2_hidden(sK5(sK2,sK3),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(sK5(sK2,sK3),X2) | r2_hidden(sK5(sK2,X2),X2)) ) | ~spl6_12),
% 0.21/0.50    inference(resolution,[],[f231,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | (~v4_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ( ! [X0] : (~sP0(sK2,X0) | ~r2_hidden(sK5(sK2,sK3),X0)) ) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl6_12 <=> ! [X0] : (~r2_hidden(sK5(sK2,sK3),X0) | ~sP0(sK2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5(sK2,sK4),X0) | ~sP0(sK2,X0)) ) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f270])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    spl6_14 <=> ! [X0] : (~r2_hidden(sK5(sK2,sK4),X0) | ~sP0(sK2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ~spl6_8 | ~spl6_12 | ~spl6_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    $false | (~spl6_8 | ~spl6_12 | ~spl6_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f274,f144])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK3),sK4) | (~spl6_12 | ~spl6_13)),
% 0.21/0.50    inference(resolution,[],[f273,f231])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    sP0(sK2,sK4) | ~spl6_13),
% 0.21/0.50    inference(resolution,[],[f268,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_pre_topc(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    v4_pre_topc(sK5(sK2,sK4),sK2) | ~spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f266])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    spl6_13 <=> v4_pre_topc(sK5(sK2,sK4),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    spl6_13 | spl6_14 | ~spl6_8 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f248,f230,f142,f270,f266])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5(sK2,sK4),X0) | v4_pre_topc(sK5(sK2,sK4),sK2) | ~sP0(sK2,X0)) ) | (~spl6_8 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f244,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,X1) | v4_pre_topc(X3,X0) | ~sP0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_8 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f242,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK4) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.50    inference(resolution,[],[f33,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ~spl6_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    $false | ~spl6_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f235,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~v2_tops_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    v2_tops_2(sK3,sK2) | ~spl6_11),
% 0.21/0.50    inference(subsumption_resolution,[],[f234,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_2(sK3,sK2) | ~spl6_11),
% 0.21/0.50    inference(resolution,[],[f233,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X1] : (~sP0(sK2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_2(X1,sK2)) )),
% 0.21/0.50    inference(resolution,[],[f52,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tops_2(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    sP0(sK2,sK3) | ~spl6_11),
% 0.21/0.50    inference(resolution,[],[f228,f42])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    v4_pre_topc(sK5(sK2,sK3),sK2) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    spl6_11 <=> v4_pre_topc(sK5(sK2,sK3),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl6_11 | spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f230,f226])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK5(sK2,sK3),X0) | v4_pre_topc(sK5(sK2,sK3),sK2) | ~sP0(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f157,f39])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.50    inference(resolution,[],[f57,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f32])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | r2_hidden(sK5(sK2,sK3),sK3)),
% 0.21/0.50    inference(resolution,[],[f112,f36])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X2] : (v2_tops_2(X2,sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | r2_hidden(sK5(sK2,X2),X2)) )),
% 0.21/0.50    inference(resolution,[],[f76,f41])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.50    inference(resolution,[],[f32,f50])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ~spl6_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    $false | ~spl6_7),
% 0.21/0.50    inference(resolution,[],[f167,f115])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl6_7),
% 0.21/0.50    inference(resolution,[],[f147,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK4))),
% 0.21/0.50    inference(resolution,[],[f34,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    r1_tarski(sK3,sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK4)) | ~r2_hidden(X1,X0)) ) | ~spl6_7),
% 0.21/0.50    inference(resolution,[],[f140,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    v1_xboole_0(sK4) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl6_7 <=> v1_xboole_0(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl6_7 | spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f121,f142,f138])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3),sK4) | v1_xboole_0(sK4)),
% 0.21/0.50    inference(resolution,[],[f120,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK2,sK3),sK4)),
% 0.21/0.50    inference(resolution,[],[f54,f115])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | m1_subset_1(X0,sK4)) )),
% 0.21/0.50    inference(resolution,[],[f53,f50])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30875)------------------------------
% 0.21/0.50  % (30875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30875)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30875)Memory used [KB]: 9978
% 0.21/0.50  % (30875)Time elapsed: 0.068 s
% 0.21/0.50  % (30875)------------------------------
% 0.21/0.50  % (30875)------------------------------
% 0.21/0.50  % (30882)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.50  % (30869)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.50  % (30863)Success in time 0.143 s
%------------------------------------------------------------------------------

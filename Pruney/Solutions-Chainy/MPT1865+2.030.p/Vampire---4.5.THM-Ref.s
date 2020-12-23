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
% DateTime   : Thu Dec  3 13:21:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 281 expanded)
%              Number of leaves         :   24 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  378 (1549 expanded)
%              Number of equality atoms :   45 ( 217 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f70,f92,f94,f146,f151,f163,f173,f181,f193,f194])).

fof(f194,plain,
    ( ~ spl7_3
    | ~ spl7_15
    | ~ spl7_16
    | spl7_13 ),
    inference(avatar_split_clause,[],[f189,f156,f170,f166,f79])).

fof(f79,plain,
    ( spl7_3
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f166,plain,
    ( spl7_15
  <=> m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f170,plain,
    ( spl7_16
  <=> r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f156,plain,
    ( spl7_13
  <=> m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f189,plain,
    ( ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_13 ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK5(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
              & v4_pre_topc(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v4_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK5(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v4_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
        & v4_pre_topc(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v4_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v4_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

% (14979)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f23,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f158,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f156])).

fof(f193,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f187,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
        | ~ v4_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v4_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                | ~ v4_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
              | ~ v4_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
          | ~ v4_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

% (14989)Refutation not found, incomplete strategy% (14989)------------------------------
% (14989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14989)Termination reason: Refutation not found, incomplete strategy

% (14989)Memory used [KB]: 10746
% (14989)Time elapsed: 0.121 s
% (14989)------------------------------
% (14989)------------------------------
% (14988)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (14982)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (15001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(f187,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_15 ),
    inference(resolution,[],[f185,f33])).

fof(f33,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl7_15 ),
    inference(resolution,[],[f183,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f183,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | spl7_15 ),
    inference(resolution,[],[f168,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f168,plain,
    ( ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f181,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f177,f33])).

fof(f177,plain,
    ( ~ r2_hidden(sK4,sK3)
    | spl7_16 ),
    inference(resolution,[],[f174,f52])).

fof(f174,plain,
    ( ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(sK3))
    | spl7_16 ),
    inference(resolution,[],[f172,f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f172,plain,
    ( ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( ~ spl7_3
    | ~ spl7_15
    | ~ spl7_16
    | spl7_14 ),
    inference(avatar_split_clause,[],[f164,f160,f170,f166,f79])).

fof(f160,plain,
    ( spl7_14
  <=> v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f164,plain,
    ( ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2)
    | spl7_14 ),
    inference(resolution,[],[f162,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK6(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f162,plain,
    ( ~ v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f154,f143,f160,f156])).

fof(f143,plain,
    ( spl7_12
  <=> k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f154,plain,
    ( ~ v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_12 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_enumset1(sK4,sK4,sK4) != k1_enumset1(sK4,sK4,sK4)
    | ~ v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_12 ),
    inference(superposition,[],[f51,f145])).

fof(f145,plain,
    ( k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f51,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_enumset1(sK4,sK4,sK4)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f34,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,(
    ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl7_11 ),
    inference(resolution,[],[f147,f30])).

% (14997)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f147,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_11 ),
    inference(resolution,[],[f141,f33])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f146,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f137,f65,f143,f140])).

fof(f65,plain,
    ( spl7_2
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X0,sK3)
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)))
        | ~ r2_hidden(sK4,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f135,f33])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK3)
        | k1_enumset1(X0,X0,X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X0,X0,X0)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f133,f47])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | ~ r2_hidden(X0,sK3)
        | k1_enumset1(X0,X0,X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X0,X0,X0))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(u1_struct_0(sK2)))
        | k1_enumset1(X1,X1,X1) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X1,X1,X1)))
        | ~ r2_hidden(X1,sK3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f71,f52])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f94,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl7_5 ),
    inference(resolution,[],[f91,f31])).

fof(f31,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_5
  <=> v2_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_3 ),
    inference(avatar_split_clause,[],[f87,f79,f89,f61])).

fof(f61,plain,
    ( spl7_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f87,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_3 ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X1] :
      ( sP0(X1,sK2)
      | ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f53,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f44,f29])).

fof(f29,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f16,f15])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f80,plain,
    ( ~ sP0(sK3,sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f70,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f63,f30])).

fof(f63,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f59,f65,f61])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0
      | ~ r1_tarski(X0,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f58,f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f40,f55])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (14991)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (14991)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 1.40/0.53  % (15007)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (14999)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (14989)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f195,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f67,f70,f92,f94,f146,f151,f163,f173,f181,f193,f194])).
% 1.40/0.54  fof(f194,plain,(
% 1.40/0.54    ~spl7_3 | ~spl7_15 | ~spl7_16 | spl7_13),
% 1.40/0.54    inference(avatar_split_clause,[],[f189,f156,f170,f166,f79])).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    spl7_3 <=> sP0(sK3,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.40/0.54  fof(f166,plain,(
% 1.40/0.54    spl7_15 <=> m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.40/0.54  fof(f170,plain,(
% 1.40/0.54    spl7_16 <=> r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.40/0.54  fof(f156,plain,(
% 1.40/0.54    spl7_13 <=> m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.40/0.54  fof(f189,plain,(
% 1.40/0.54    ~r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) | ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_13),
% 1.40/0.54    inference(resolution,[],[f158,f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ( ! [X4,X0,X1] : (m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v4_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f26,f25])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v4_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v4_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 1.40/0.54    inference(rectify,[],[f23])).
% 1.40/0.54  % (14979)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 1.40/0.54    inference(nnf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.54  fof(f158,plain,(
% 1.40/0.54    ~m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_13),
% 1.40/0.54    inference(avatar_component_clause,[],[f156])).
% 1.40/0.54  fof(f193,plain,(
% 1.40/0.54    spl7_15),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f191])).
% 1.40/0.54  fof(f191,plain,(
% 1.40/0.54    $false | spl7_15),
% 1.40/0.54    inference(resolution,[],[f187,f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ((! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f20,f19,f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.55  % (14989)Refutation not found, incomplete strategy% (14989)------------------------------
% 1.40/0.55  % (14989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14989)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14989)Memory used [KB]: 10746
% 1.40/0.55  % (14989)Time elapsed: 0.121 s
% 1.40/0.55  % (14989)------------------------------
% 1.40/0.55  % (14989)------------------------------
% 1.40/0.55  % (14988)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (14982)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.55  % (15001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.55  fof(f10,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.48/0.55    inference(flattening,[],[f9])).
% 1.48/0.55  fof(f9,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,negated_conjecture,(
% 1.48/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.48/0.55    inference(negated_conjecture,[],[f7])).
% 1.48/0.55  fof(f7,conjecture,(
% 1.48/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 1.48/0.55  fof(f187,plain,(
% 1.48/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_15),
% 1.48/0.55    inference(resolution,[],[f185,f33])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    r2_hidden(sK4,sK3)),
% 1.48/0.55    inference(cnf_transformation,[],[f21])).
% 1.48/0.55  fof(f185,plain,(
% 1.48/0.55    ( ! [X0] : (~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl7_15),
% 1.48/0.55    inference(resolution,[],[f183,f47])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f14])).
% 1.48/0.55  fof(f14,plain,(
% 1.48/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.48/0.55  fof(f183,plain,(
% 1.48/0.55    ~r2_hidden(sK4,u1_struct_0(sK2)) | spl7_15),
% 1.48/0.55    inference(resolution,[],[f168,f52])).
% 1.48/0.55  fof(f52,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f46,f50])).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f35,f45])).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f2])).
% 1.48/0.55  fof(f2,axiom,(
% 1.48/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f1])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f13,plain,(
% 1.48/0.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.48/0.55  fof(f168,plain,(
% 1.48/0.55    ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_15),
% 1.48/0.55    inference(avatar_component_clause,[],[f166])).
% 1.48/0.55  fof(f181,plain,(
% 1.48/0.55    spl7_16),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f179])).
% 1.48/0.55  fof(f179,plain,(
% 1.48/0.55    $false | spl7_16),
% 1.48/0.55    inference(resolution,[],[f177,f33])).
% 1.48/0.55  fof(f177,plain,(
% 1.48/0.55    ~r2_hidden(sK4,sK3) | spl7_16),
% 1.48/0.55    inference(resolution,[],[f174,f52])).
% 1.48/0.55  fof(f174,plain,(
% 1.48/0.55    ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(sK3)) | spl7_16),
% 1.48/0.55    inference(resolution,[],[f172,f48])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.48/0.55    inference(nnf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.55  fof(f172,plain,(
% 1.48/0.55    ~r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) | spl7_16),
% 1.48/0.55    inference(avatar_component_clause,[],[f170])).
% 1.48/0.55  fof(f173,plain,(
% 1.48/0.55    ~spl7_3 | ~spl7_15 | ~spl7_16 | spl7_14),
% 1.48/0.55    inference(avatar_split_clause,[],[f164,f160,f170,f166,f79])).
% 1.48/0.55  fof(f160,plain,(
% 1.48/0.55    spl7_14 <=> v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.48/0.55  fof(f164,plain,(
% 1.48/0.55    ~r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) | ~m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2) | spl7_14),
% 1.48/0.55    inference(resolution,[],[f162,f39])).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ( ! [X4,X0,X1] : (v4_pre_topc(sK6(X0,X1,X4),X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f162,plain,(
% 1.48/0.55    ~v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2) | spl7_14),
% 1.48/0.55    inference(avatar_component_clause,[],[f160])).
% 1.48/0.55  fof(f163,plain,(
% 1.48/0.55    ~spl7_13 | ~spl7_14 | ~spl7_12),
% 1.48/0.55    inference(avatar_split_clause,[],[f154,f143,f160,f156])).
% 1.48/0.55  fof(f143,plain,(
% 1.48/0.55    spl7_12 <=> k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.48/0.55  fof(f154,plain,(
% 1.48/0.55    ~v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_12),
% 1.48/0.55    inference(trivial_inequality_removal,[],[f152])).
% 1.48/0.55  fof(f152,plain,(
% 1.48/0.55    k1_enumset1(sK4,sK4,sK4) != k1_enumset1(sK4,sK4,sK4) | ~v4_pre_topc(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_12),
% 1.48/0.55    inference(superposition,[],[f51,f145])).
% 1.48/0.55  fof(f145,plain,(
% 1.48/0.55    k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4))) | ~spl7_12),
% 1.48/0.55    inference(avatar_component_clause,[],[f143])).
% 1.48/0.55  fof(f51,plain,(
% 1.48/0.55    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_enumset1(sK4,sK4,sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.55    inference(definition_unfolding,[],[f34,f50])).
% 1.48/0.55  fof(f34,plain,(
% 1.48/0.55    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f21])).
% 1.48/0.55  fof(f151,plain,(
% 1.48/0.55    ~spl7_11),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f149])).
% 1.48/0.55  fof(f149,plain,(
% 1.48/0.55    $false | ~spl7_11),
% 1.48/0.55    inference(resolution,[],[f147,f30])).
% 1.48/0.55  % (14997)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.55  fof(f147,plain,(
% 1.48/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_11),
% 1.48/0.55    inference(resolution,[],[f141,f33])).
% 1.48/0.56  fof(f141,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_11),
% 1.48/0.56    inference(avatar_component_clause,[],[f140])).
% 1.48/0.56  fof(f140,plain,(
% 1.48/0.56    spl7_11 <=> ! [X0] : (~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.48/0.56  fof(f146,plain,(
% 1.48/0.56    spl7_11 | spl7_12 | ~spl7_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f137,f65,f143,f140])).
% 1.48/0.56  fof(f65,plain,(
% 1.48/0.56    spl7_2 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X0,sK3) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.48/0.56  fof(f137,plain,(
% 1.48/0.56    ( ! [X0] : (k1_enumset1(sK4,sK4,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(sK4,sK4,sK4))) | ~r2_hidden(sK4,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f135,f33])).
% 1.48/0.56  fof(f135,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | k1_enumset1(X0,X0,X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X0,X0,X0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f133,f47])).
% 1.48/0.56  fof(f133,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK3) | k1_enumset1(X0,X0,X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X0,X0,X0)))) ) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f74,f52])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    ( ! [X1] : (~m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(u1_struct_0(sK2))) | k1_enumset1(X1,X1,X1) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_enumset1(X1,X1,X1))) | ~r2_hidden(X1,sK3)) ) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f71,f52])).
% 1.48/0.56  fof(f71,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK3)) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f66,f48])).
% 1.48/0.56  fof(f66,plain,(
% 1.48/0.56    ( ! [X0] : (~r1_tarski(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0) ) | ~spl7_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f65])).
% 1.48/0.56  fof(f94,plain,(
% 1.48/0.56    spl7_5),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f93])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    $false | spl7_5),
% 1.48/0.56    inference(resolution,[],[f91,f31])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    v2_tex_2(sK3,sK2)),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    ~v2_tex_2(sK3,sK2) | spl7_5),
% 1.48/0.56    inference(avatar_component_clause,[],[f89])).
% 1.48/0.56  fof(f89,plain,(
% 1.48/0.56    spl7_5 <=> v2_tex_2(sK3,sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.48/0.56  fof(f92,plain,(
% 1.48/0.56    ~spl7_1 | ~spl7_5 | spl7_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f87,f79,f89,f61])).
% 1.48/0.56  fof(f61,plain,(
% 1.48/0.56    spl7_1 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    ~v2_tex_2(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_3),
% 1.48/0.56    inference(resolution,[],[f80,f55])).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    ( ! [X1] : (sP0(X1,sK2) | ~v2_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.56    inference(resolution,[],[f53,f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.48/0.56    inference(nnf_transformation,[],[f16])).
% 1.48/0.56  fof(f16,plain,(
% 1.48/0.56    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.48/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.56    inference(resolution,[],[f44,f29])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    l1_pre_topc(sK2)),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f17])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(definition_folding,[],[f12,f16,f15])).
% 1.48/0.56  fof(f12,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(flattening,[],[f11])).
% 1.48/0.56  fof(f11,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.48/0.56  fof(f80,plain,(
% 1.48/0.56    ~sP0(sK3,sK2) | spl7_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f79])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    spl7_1),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f68])).
% 1.48/0.56  fof(f68,plain,(
% 1.48/0.56    $false | spl7_1),
% 1.48/0.56    inference(resolution,[],[f63,f30])).
% 1.48/0.56  fof(f63,plain,(
% 1.48/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f61])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ~spl7_1 | spl7_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f59,f65,f61])).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 | ~r1_tarski(X0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.56    inference(resolution,[],[f58,f31])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v2_tex_2(X1,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),X1,sK6(X1,sK2,X0)) = X0 | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.48/0.56    inference(resolution,[],[f40,f55])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4) )),
% 1.48/0.56    inference(cnf_transformation,[],[f27])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (14991)------------------------------
% 1.48/0.56  % (14991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (14991)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (14991)Memory used [KB]: 6268
% 1.48/0.56  % (14991)Time elapsed: 0.115 s
% 1.48/0.56  % (14991)------------------------------
% 1.48/0.56  % (14991)------------------------------
% 1.48/0.56  % (14978)Success in time 0.198 s
%------------------------------------------------------------------------------

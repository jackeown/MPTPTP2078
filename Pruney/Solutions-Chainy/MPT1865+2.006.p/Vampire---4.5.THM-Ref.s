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
% DateTime   : Thu Dec  3 13:21:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 ( 913 expanded)
%              Number of equality atoms :   34 ( 129 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f204,f208])).

fof(f208,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl11_2 ),
    inference(subsumption_resolution,[],[f205,f50])).

fof(f50,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
        | ~ v4_pre_topc(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f11,f23,f22,f21])).

fof(f21,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                  | ~ v4_pre_topc(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                | ~ v4_pre_topc(X3,sK4)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & v2_tex_2(X1,sK4)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
              | ~ v4_pre_topc(X3,sK4)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & r2_hidden(X2,sK5)
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & v2_tex_2(sK5,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
            | ~ v4_pre_topc(X3,sK4)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & r2_hidden(X2,sK5)
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
          | ~ v4_pre_topc(X3,sK4)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & r2_hidden(sK6,sK5)
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f205,plain,
    ( ~ r2_hidden(sK6,sK5)
    | spl11_2 ),
    inference(resolution,[],[f181,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f181,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl11_2
  <=> r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f204,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f199,f50])).

fof(f199,plain,
    ( ~ r2_hidden(sK6,sK5)
    | spl11_1 ),
    inference(resolution,[],[f190,f89])).

fof(f89,plain,(
    r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK6,X0) )
    | spl11_1 ),
    inference(resolution,[],[f185,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f185,plain,
    ( ~ r2_hidden(sK6,u1_struct_0(sK4))
    | spl11_1 ),
    inference(resolution,[],[f177,f82])).

fof(f177,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl11_1
  <=> r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f182,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f173,f179,f175])).

fof(f173,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)
    | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f170,f116])).

fof(f116,plain,(
    sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f115,f48])).

fof(f48,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f115,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | sP1(sK4,sK5) ),
    inference(resolution,[],[f113,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f113,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f111,f46])).

fof(f46,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f63,f47])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f17,f16,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f170,plain,
    ( ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)
    | ~ sP1(sK4,sK5)
    | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
    inference(resolution,[],[f157,f151])).

fof(f151,plain,(
    ~ sP0(k1_enumset1(sK6,sK6,sK6),sK5,sK4) ),
    inference(equality_resolution,[],[f149])).

% (14174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f149,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f148,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
          & v4_pre_topc(sK8(X0,X1,X2),X2)
          & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v4_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
        & v4_pre_topc(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v4_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f148,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f147,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK8(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f147,plain,(
    ! [X0] :
      ( k1_enumset1(sK6,sK6,sK6) != X0
      | ~ v4_pre_topc(sK8(X0,sK5,sK4),sK4)
      | ~ m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP0(X0,sK5,sK4) ) ),
    inference(superposition,[],[f79,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_enumset1(sK6,sK6,sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f51,f78])).

fof(f51,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r1_tarski(X0,X1)
      | ~ sP1(X2,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f55,f77])).

% (14151)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | sP0(X3,X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK7(X0,X1),X1,X0)
          & r1_tarski(sK7(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK7(X0,X1),X1,X0)
        & r1_tarski(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14162)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (14179)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (14153)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (14167)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (14153)Refutation not found, incomplete strategy% (14153)------------------------------
% 0.22/0.52  % (14153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14153)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14153)Memory used [KB]: 10746
% 0.22/0.52  % (14153)Time elapsed: 0.098 s
% 0.22/0.52  % (14153)------------------------------
% 0.22/0.52  % (14153)------------------------------
% 0.22/0.52  % (14156)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (14179)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (14160)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (14155)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (14173)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f182,f204,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    spl11_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    $false | spl11_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f205,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    r2_hidden(sK6,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ((! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f11,f23,f22,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) => (! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ~r2_hidden(sK6,sK5) | spl11_2),
% 0.22/0.53    inference(resolution,[],[f181,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f75,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) | spl11_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl11_2 <=> r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    spl11_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    $false | spl11_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f199,f50])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    ~r2_hidden(sK6,sK5) | spl11_1),
% 0.22/0.53    inference(resolution,[],[f190,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    r1_tarski(sK5,u1_struct_0(sK4))),
% 0.22/0.53    inference(resolution,[],[f76,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK6,X0)) ) | spl11_1),
% 0.22/0.53    inference(resolution,[],[f185,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~r2_hidden(sK6,u1_struct_0(sK4)) | spl11_1),
% 0.22/0.53    inference(resolution,[],[f177,f82])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) | spl11_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f175])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    spl11_1 <=> r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ~spl11_1 | ~spl11_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f173,f179,f175])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) | ~r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    sP1(sK4,sK5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f115,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v2_tex_2(sK5,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    ~v2_tex_2(sK5,sK4) | sP1(sK4,sK5)),
% 0.22/0.53    inference(resolution,[],[f113,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~v2_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.22/0.53    inference(rectify,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    sP2(sK5,sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f111,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    l1_pre_topc(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.22/0.53    inference(resolution,[],[f63,f47])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(definition_folding,[],[f13,f17,f16,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ~r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) | ~sP1(sK4,sK5) | ~r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4))),
% 0.22/0.53    inference(resolution,[],[f157,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ~sP0(k1_enumset1(sK6,sK6,sK6),sK5,sK4)),
% 0.22/0.53    inference(equality_resolution,[],[f149])).
% 0.22/0.53  % (14174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~sP0(X0,sK5,sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f148,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 & v4_pre_topc(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 & v4_pre_topc(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP0(X0,sK5,sK4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f147,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_pre_topc(sK8(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X0] : (k1_enumset1(sK6,sK6,sK6) != X0 | ~v4_pre_topc(sK8(X0,sK5,sK4),sK4) | ~m1_subset_1(sK8(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP0(X0,sK5,sK4)) )),
% 0.22/0.53    inference(superposition,[],[f79,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_enumset1(sK6,sK6,sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f51,f78])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r1_tarski(X0,X1) | ~sP1(X2,X1) | ~r1_tarski(X0,u1_struct_0(X2))) )),
% 0.22/0.53    inference(resolution,[],[f55,f77])).
% 0.22/0.53  % (14151)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | sP0(X3,X1,X0) | ~sP1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK7(X0,X1),X1,X0) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK7(X0,X1),X1,X0) & r1_tarski(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f16])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (14179)------------------------------
% 0.22/0.53  % (14179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14179)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (14179)Memory used [KB]: 6268
% 0.22/0.53  % (14179)Time elapsed: 0.111 s
% 0.22/0.53  % (14179)------------------------------
% 0.22/0.53  % (14179)------------------------------
% 0.22/0.53  % (14150)Success in time 0.167 s
%------------------------------------------------------------------------------

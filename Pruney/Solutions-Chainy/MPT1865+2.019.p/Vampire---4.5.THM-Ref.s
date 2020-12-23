%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:03 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 221 expanded)
%              Number of leaves         :   26 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  441 (1167 expanded)
%              Number of equality atoms :   54 ( 156 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f76,f86,f92,f107,f112,f117,f128,f134,f136,f138])).

fof(f138,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_15
    | spl6_14 ),
    inference(avatar_split_clause,[],[f137,f126,f132,f105,f59,f63,f67])).

fof(f67,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f63,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f59,plain,
    ( spl6_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f105,plain,
    ( spl6_11
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f132,plain,
    ( spl6_15
  <=> r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f126,plain,
    ( spl6_14
  <=> v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f137,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_14 ),
    inference(resolution,[],[f127,f38])).

% (7943)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f38,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK5(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
                    & v4_pre_topc(sK5(X0,X1,X4),X0)
                    & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X0)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
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
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f127,plain,
    ( ~ v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f136,plain,
    ( ~ spl6_1
    | spl6_15 ),
    inference(avatar_split_clause,[],[f135,f132,f51])).

fof(f51,plain,
    ( spl6_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f135,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl6_15 ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f133,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_15
    | spl6_13 ),
    inference(avatar_split_clause,[],[f129,f123,f132,f105,f59,f63,f67])).

fof(f123,plain,
    ( spl6_13
  <=> m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f129,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_13 ),
    inference(resolution,[],[f124,f37])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f124,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f128,plain,
    ( ~ spl6_13
    | ~ spl6_14
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f121,f115,f126,f123])).

fof(f115,plain,
    ( spl6_12
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f121,plain,
    ( ~ v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2)
    | ~ v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(superposition,[],[f46,f116])).

fof(f116,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f46,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_tarski(sK2,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
        | ~ v4_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
          | ~ v4_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f117,plain,
    ( ~ spl6_1
    | spl6_12
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f113,f105,f74,f115,f51])).

fof(f74,plain,
    ( spl6_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f113,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2)))
    | ~ r2_hidden(sK2,sK1)
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f106,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(X0,X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f106,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f108,f98,f51,f55,f59,f63,f67])).

fof(f55,plain,
    ( spl6_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f98,plain,
    ( spl6_9
  <=> m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f108,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl6_9 ),
    inference(resolution,[],[f99,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f99,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f107,plain,
    ( ~ spl6_9
    | spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f95,f90,f105,f98])).

fof(f90,plain,
    ( spl6_8
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f95,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(superposition,[],[f45,f91])).

fof(f91,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f92,plain,
    ( ~ spl6_1
    | spl6_8
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f87,f84,f55,f90,f51])).

fof(f84,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f87,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,sK1)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( ~ spl6_4
    | spl6_7
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f82,f67,f59,f84,f63])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) )
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f81,f60])).

fof(f60,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),X1,sK3(sK0,X1,X0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f47,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) = k2_tarski(X2,X2) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( ~ spl6_4
    | spl6_6
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f71,f67,f59,f74,f63])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 )
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f60])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,sK5(sK0,X1,X0)) = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f39,f68])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f51])).

fof(f32,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.21/0.52  % (7947)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.53  % (7935)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.53  % (7953)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.53  % (7945)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (7953)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % (7962)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (7938)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.54  % (7948)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.54  % (7936)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (7961)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.54  % (7937)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.55  % (7956)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.55  % (7934)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.55  % (7951)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (7942)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.55  % (7954)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.55  % (7940)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.55  % (7946)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.55  % (7944)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f139,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f76,f86,f92,f107,f112,f117,f128,f134,f136,f138])).
% 1.33/0.55  fof(f138,plain,(
% 1.33/0.55    ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_11 | ~spl6_15 | spl6_14),
% 1.33/0.55    inference(avatar_split_clause,[],[f137,f126,f132,f105,f59,f63,f67])).
% 1.33/0.55  fof(f67,plain,(
% 1.33/0.55    spl6_5 <=> l1_pre_topc(sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    spl6_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    spl6_3 <=> v2_tex_2(sK1,sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.33/0.55  fof(f105,plain,(
% 1.33/0.55    spl6_11 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.33/0.55  fof(f132,plain,(
% 1.33/0.55    spl6_15 <=> r1_tarski(k2_tarski(sK2,sK2),sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.33/0.55  fof(f126,plain,(
% 1.33/0.55    spl6_14 <=> v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    ~r1_tarski(k2_tarski(sK2,sK2),sK1) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_14),
% 1.33/0.55    inference(resolution,[],[f127,f38])).
% 1.33/0.55  % (7943)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ( ! [X4,X0,X1] : (v4_pre_topc(sK5(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f25,f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(rectify,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(nnf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(flattening,[],[f13])).
% 1.33/0.55  fof(f13,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    ~v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0) | spl6_14),
% 1.33/0.55    inference(avatar_component_clause,[],[f126])).
% 1.33/0.55  fof(f136,plain,(
% 1.33/0.55    ~spl6_1 | spl6_15),
% 1.33/0.55    inference(avatar_split_clause,[],[f135,f132,f51])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    spl6_1 <=> r2_hidden(sK2,sK1)),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.33/0.55  fof(f135,plain,(
% 1.33/0.55    ~r2_hidden(sK2,sK1) | spl6_15),
% 1.33/0.55    inference(resolution,[],[f133,f48])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f44,f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.33/0.55    inference(nnf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.33/0.55  fof(f133,plain,(
% 1.33/0.55    ~r1_tarski(k2_tarski(sK2,sK2),sK1) | spl6_15),
% 1.33/0.55    inference(avatar_component_clause,[],[f132])).
% 1.33/0.55  fof(f134,plain,(
% 1.33/0.55    ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_11 | ~spl6_15 | spl6_13),
% 1.33/0.55    inference(avatar_split_clause,[],[f129,f123,f132,f105,f59,f63,f67])).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    spl6_13 <=> m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.33/0.55  fof(f129,plain,(
% 1.33/0.55    ~r1_tarski(k2_tarski(sK2,sK2),sK1) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_13),
% 1.33/0.55    inference(resolution,[],[f124,f37])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    ( ! [X4,X0,X1] : (m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f124,plain,(
% 1.33/0.55    ~m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_13),
% 1.33/0.55    inference(avatar_component_clause,[],[f123])).
% 1.33/0.55  fof(f128,plain,(
% 1.33/0.55    ~spl6_13 | ~spl6_14 | ~spl6_12),
% 1.33/0.55    inference(avatar_split_clause,[],[f121,f115,f126,f123])).
% 1.33/0.55  fof(f115,plain,(
% 1.33/0.55    spl6_12 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.33/0.55  fof(f121,plain,(
% 1.33/0.55    ~v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_12),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f118])).
% 1.33/0.55  fof(f118,plain,(
% 1.33/0.55    k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) | ~v4_pre_topc(sK5(sK0,sK1,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(sK5(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_12),
% 1.33/0.55    inference(superposition,[],[f46,f116])).
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2))) | ~spl6_12),
% 1.33/0.55    inference(avatar_component_clause,[],[f115])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_tarski(sK2,sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.55    inference(definition_unfolding,[],[f33,f34])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ((! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 1.33/0.55  fof(f16,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f10,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.55    inference(flattening,[],[f9])).
% 1.33/0.55  fof(f9,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,negated_conjecture,(
% 1.33/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.33/0.55    inference(negated_conjecture,[],[f6])).
% 1.33/0.55  fof(f6,conjecture,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 1.33/0.55  fof(f117,plain,(
% 1.33/0.55    ~spl6_1 | spl6_12 | ~spl6_6 | ~spl6_11),
% 1.33/0.55    inference(avatar_split_clause,[],[f113,f105,f74,f115,f51])).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    spl6_6 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 | ~r1_tarski(X0,sK1))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.33/0.55  fof(f113,plain,(
% 1.33/0.55    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(sK2,sK2))) | ~r2_hidden(sK2,sK1) | (~spl6_6 | ~spl6_11)),
% 1.33/0.55    inference(resolution,[],[f106,f77])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,k2_tarski(X0,X0))) | ~r2_hidden(X0,sK1)) ) | ~spl6_6),
% 1.33/0.55    inference(resolution,[],[f75,f48])).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_6),
% 1.33/0.55    inference(avatar_component_clause,[],[f74])).
% 1.33/0.55  fof(f106,plain,(
% 1.33/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_11),
% 1.33/0.55    inference(avatar_component_clause,[],[f105])).
% 1.33/0.55  fof(f112,plain,(
% 1.33/0.55    ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_1 | spl6_9),
% 1.33/0.55    inference(avatar_split_clause,[],[f108,f98,f51,f55,f59,f63,f67])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    spl6_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.33/0.55  fof(f98,plain,(
% 1.33/0.55    spl6_9 <=> m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.33/0.55  fof(f108,plain,(
% 1.33/0.55    ~r2_hidden(sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl6_9),
% 1.33/0.55    inference(resolution,[],[f99,f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (! [X2] : ((k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X2,X1,X0] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f12,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(flattening,[],[f11])).
% 1.33/0.55  fof(f11,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,plain,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)) & r2_hidden(X2,X1))))))),
% 1.33/0.55    inference(pure_predicate_removal,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 1.33/0.55  fof(f99,plain,(
% 1.33/0.55    ~m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_9),
% 1.33/0.55    inference(avatar_component_clause,[],[f98])).
% 1.33/0.55  fof(f107,plain,(
% 1.33/0.55    ~spl6_9 | spl6_11 | ~spl6_8),
% 1.33/0.55    inference(avatar_split_clause,[],[f95,f90,f105,f98])).
% 1.33/0.55  fof(f90,plain,(
% 1.33/0.55    spl6_8 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.33/0.55  fof(f95,plain,(
% 1.33/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_8),
% 1.33/0.55    inference(superposition,[],[f45,f91])).
% 1.33/0.55  fof(f91,plain,(
% 1.33/0.55    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) | ~spl6_8),
% 1.33/0.55    inference(avatar_component_clause,[],[f90])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.33/0.55  fof(f92,plain,(
% 1.33/0.55    ~spl6_1 | spl6_8 | ~spl6_2 | ~spl6_7),
% 1.33/0.55    inference(avatar_split_clause,[],[f87,f84,f55,f90,f51])).
% 1.33/0.55  fof(f84,plain,(
% 1.33/0.55    spl6_7 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) | ~r2_hidden(X0,sK1))),
% 1.33/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.33/0.55  fof(f87,plain,(
% 1.33/0.55    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,sK2)) | ~r2_hidden(sK2,sK1) | (~spl6_2 | ~spl6_7)),
% 1.33/0.55    inference(resolution,[],[f85,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_2),
% 1.33/0.55    inference(avatar_component_clause,[],[f55])).
% 1.33/0.55  fof(f85,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) | ~r2_hidden(X0,sK1)) ) | ~spl6_7),
% 1.33/0.55    inference(avatar_component_clause,[],[f84])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ~spl6_4 | spl6_7 | ~spl6_3 | ~spl6_5),
% 1.33/0.55    inference(avatar_split_clause,[],[f82,f67,f59,f84,f63])).
% 1.33/0.55  fof(f82,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))) ) | (~spl6_3 | ~spl6_5)),
% 1.33/0.55    inference(resolution,[],[f81,f60])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    v2_tex_2(sK1,sK0) | ~spl6_3),
% 1.33/0.55    inference(avatar_component_clause,[],[f59])).
% 1.33/0.55  fof(f81,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),X1,sK3(sK0,X1,X0))) ) | ~spl6_5),
% 1.33/0.55    inference(resolution,[],[f47,f68])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    l1_pre_topc(sK0) | ~spl6_5),
% 1.33/0.55    inference(avatar_component_clause,[],[f67])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) = k2_tarski(X2,X2)) )),
% 1.33/0.55    inference(definition_unfolding,[],[f36,f34])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f21])).
% 1.33/0.55  fof(f76,plain,(
% 1.33/0.55    ~spl6_4 | spl6_6 | ~spl6_3 | ~spl6_5),
% 1.33/0.55    inference(avatar_split_clause,[],[f71,f67,f59,f74,f63])).
% 1.33/0.55  fof(f71,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0) ) | (~spl6_3 | ~spl6_5)),
% 1.33/0.55    inference(resolution,[],[f70,f60])).
% 1.33/0.55  fof(f70,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,sK5(sK0,X1,X0)) = X0) ) | ~spl6_5),
% 1.33/0.55    inference(resolution,[],[f39,f68])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    spl6_5),
% 1.33/0.55    inference(avatar_split_clause,[],[f28,f67])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    l1_pre_topc(sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    spl6_4),
% 1.33/0.55    inference(avatar_split_clause,[],[f29,f63])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    spl6_3),
% 1.33/0.55    inference(avatar_split_clause,[],[f30,f59])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    v2_tex_2(sK1,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    spl6_2),
% 1.33/0.55    inference(avatar_split_clause,[],[f31,f55])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    spl6_1),
% 1.33/0.55    inference(avatar_split_clause,[],[f32,f51])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    r2_hidden(sK2,sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (7953)------------------------------
% 1.33/0.55  % (7953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (7953)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (7953)Memory used [KB]: 10746
% 1.33/0.55  % (7953)Time elapsed: 0.121 s
% 1.33/0.55  % (7953)------------------------------
% 1.33/0.55  % (7953)------------------------------
% 1.33/0.55  % (7939)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.56  % (7933)Success in time 0.194 s
%------------------------------------------------------------------------------

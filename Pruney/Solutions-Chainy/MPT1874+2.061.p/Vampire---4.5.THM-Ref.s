%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 199 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  347 (1035 expanded)
%              Number of equality atoms :   35 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f138,f178,f180,f182,f184,f187,f190,f192,f196,f250])).

fof(f250,plain,
    ( spl4_13
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_13
    | ~ spl4_14 ),
    inference(resolution,[],[f246,f55])).

fof(f55,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f246,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl4_13
    | ~ spl4_14 ),
    inference(resolution,[],[f225,f176])).

fof(f176,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_14
  <=> r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tarski(sK2,sK2),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | spl4_13 ),
    inference(resolution,[],[f223,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f223,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),u1_struct_0(sK0))
    | spl4_13 ),
    inference(resolution,[],[f173,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f173,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_13
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f196,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl4_14 ),
    inference(resolution,[],[f193,f39])).

fof(f39,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f193,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl4_14 ),
    inference(resolution,[],[f177,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f177,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f192,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f133,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f190,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f156,f36])).

fof(f156,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f187,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f185,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_6 ),
    inference(resolution,[],[f137,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f137,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f184,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f160,f37])).

fof(f37,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_10
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f182,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f152,f35])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f180,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f148,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f178,plain,
    ( spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_14
    | spl4_3 ),
    inference(avatar_split_clause,[],[f143,f69,f175,f171,f158,f154,f150,f146,f131])).

fof(f69,plain,
    ( spl4_3
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f143,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2)
    | ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_3 ),
    inference(superposition,[],[f71,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f71,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f138,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f129,f61,f135,f131])).

fof(f61,plain,
    ( spl4_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f129,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f63,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl4_2 ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f69,f65,f61])).

fof(f58,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (17714)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f40,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:04:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (17707)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.45  % (17709)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (17715)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (17716)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (17713)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (17718)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (17707)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f251,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f72,f76,f138,f178,f180,f182,f184,f187,f190,f192,f196,f250])).
% 0.22/0.46  fof(f250,plain,(
% 0.22/0.46    spl4_13 | ~spl4_14),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f248])).
% 0.22/0.46  fof(f248,plain,(
% 0.22/0.46    $false | (spl4_13 | ~spl4_14)),
% 0.22/0.46    inference(resolution,[],[f246,f55])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.46    inference(resolution,[],[f50,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26,f25,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.47    inference(nnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f246,plain,(
% 0.22/0.47    ~r1_tarski(sK1,u1_struct_0(sK0)) | (spl4_13 | ~spl4_14)),
% 0.22/0.47    inference(resolution,[],[f225,f176])).
% 0.22/0.47  fof(f176,plain,(
% 0.22/0.47    r1_tarski(k2_tarski(sK2,sK2),sK1) | ~spl4_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f175])).
% 0.22/0.47  fof(f175,plain,(
% 0.22/0.47    spl4_14 <=> r1_tarski(k2_tarski(sK2,sK2),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.47  fof(f225,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(k2_tarski(sK2,sK2),X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | spl4_13),
% 0.22/0.47    inference(resolution,[],[f223,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.47  fof(f223,plain,(
% 0.22/0.47    ~r1_tarski(k2_tarski(sK2,sK2),u1_struct_0(sK0)) | spl4_13),
% 0.22/0.47    inference(resolution,[],[f173,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f171])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    spl4_13 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.47  fof(f196,plain,(
% 0.22/0.47    spl4_14),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f195])).
% 0.22/0.47  fof(f195,plain,(
% 0.22/0.47    $false | spl4_14),
% 0.22/0.47    inference(resolution,[],[f193,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    r2_hidden(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f193,plain,(
% 0.22/0.47    ~r2_hidden(sK2,sK1) | spl4_14),
% 0.22/0.47    inference(resolution,[],[f177,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f49,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.47  fof(f177,plain,(
% 0.22/0.47    ~r1_tarski(k2_tarski(sK2,sK2),sK1) | spl4_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f175])).
% 0.22/0.47  fof(f192,plain,(
% 0.22/0.47    ~spl4_5),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.47  fof(f191,plain,(
% 0.22/0.47    $false | ~spl4_5),
% 0.22/0.47    inference(resolution,[],[f133,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ~v2_struct_0(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    v2_struct_0(sK0) | ~spl4_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f131])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    spl4_5 <=> v2_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.47  fof(f190,plain,(
% 0.22/0.47    spl4_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    $false | spl4_9),
% 0.22/0.47    inference(resolution,[],[f156,f36])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f154])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    spl4_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    spl4_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    $false | spl4_6),
% 0.22/0.47    inference(resolution,[],[f185,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f185,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | spl4_6),
% 0.22/0.47    inference(resolution,[],[f137,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ~l1_struct_0(sK0) | spl4_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f135])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    spl4_6 <=> l1_struct_0(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.47  fof(f184,plain,(
% 0.22/0.47    spl4_10),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.47  fof(f183,plain,(
% 0.22/0.47    $false | spl4_10),
% 0.22/0.47    inference(resolution,[],[f160,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    v2_tex_2(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ~v2_tex_2(sK1,sK0) | spl4_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f158])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    spl4_10 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.47  fof(f182,plain,(
% 0.22/0.47    spl4_8),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.47  fof(f181,plain,(
% 0.22/0.47    $false | spl4_8),
% 0.22/0.47    inference(resolution,[],[f152,f35])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | spl4_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f150])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    spl4_8 <=> l1_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    spl4_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f179])).
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    $false | spl4_7),
% 0.22/0.47    inference(resolution,[],[f148,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    v2_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ~v2_pre_topc(sK0) | spl4_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f146])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    spl4_7 <=> v2_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_13 | ~spl4_14 | spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f143,f69,f175,f171,f158,f154,f150,f146,f131])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl4_3 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    ~r1_tarski(k2_tarski(sK2,sK2),sK1) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_3),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f140])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) | ~r1_tarski(k2_tarski(sK2,sK2),sK1) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_3),
% 0.22/0.47    inference(superposition,[],[f71,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(rectify,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f69])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    spl4_5 | ~spl4_6 | ~spl4_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f129,f61,f135,f131])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl4_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.47    inference(resolution,[],[f63,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl4_2),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    $false | spl4_2),
% 0.22/0.47    inference(resolution,[],[f67,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ~m1_subset_1(sK2,u1_struct_0(sK0)) | spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f58,f69,f65,f61])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.47    inference(superposition,[],[f40,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f48,f41])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  % (17714)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17707)------------------------------
% 0.22/0.47  % (17707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17707)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17707)Memory used [KB]: 6268
% 0.22/0.47  % (17707)Time elapsed: 0.050 s
% 0.22/0.47  % (17707)------------------------------
% 0.22/0.47  % (17707)------------------------------
% 0.22/0.47  % (17704)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (17702)Success in time 0.105 s
%------------------------------------------------------------------------------

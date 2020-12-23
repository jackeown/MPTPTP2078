%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 192 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  379 (1216 expanded)
%              Number of equality atoms :   42 ( 169 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f212,f218])).

fof(f218,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f216,f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f9,f23,f22,f21])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

fof(f216,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f44,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f214,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,sK5)
    | ~ spl10_5 ),
    inference(resolution,[],[f207,f173])).

fof(f173,plain,(
    ! [X12] :
      ( sP0(X12,sK5,sK4)
      | ~ m1_subset_1(X12,u1_struct_0(sK4))
      | ~ r2_hidden(X12,sK5) ) ),
    inference(subsumption_resolution,[],[f172,f41])).

fof(f41,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f172,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK5)
      | ~ m1_subset_1(X12,u1_struct_0(sK4))
      | sP0(X12,sK5,sK4)
      | ~ l1_pre_topc(sK4) ) ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f43,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f168,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,sK5)
      | ~ m1_subset_1(X12,u1_struct_0(sK4))
      | ~ v2_tex_2(sK5,sK4)
      | sP0(X12,sK5,sK4)
      | ~ l1_pre_topc(sK4) ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | sP0(X2,X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X2,X1,X0)
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f207,plain,
    ( ! [X2] : ~ sP0(sK6,X2,sK4)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl10_5
  <=> ! [X2] : ~ sP0(sK6,X2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f212,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f204,f112,f206])).

fof(f112,plain,
    ( spl10_2
  <=> r1_tarski(k2_tarski(sK6,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f204,plain,
    ( ! [X0] : ~ sP0(sK6,X0,sK4)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f203,f75])).

fof(f75,plain,(
    sP2(sK4,sK5) ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f74,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | sP2(sK4,sK5) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f72,plain,(
    sP3(sK5,sK4) ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f70,plain,
    ( sP3(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP3(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( sP1(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f203,plain,
    ( ! [X0] :
        ( ~ sP0(sK6,X0,sK4)
        | ~ sP2(sK4,sK5) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f199,f113])).

fof(f113,plain,
    ( r1_tarski(k2_tarski(sK6,sK6),sK5)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f199,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_tarski(sK6,sK6),sK5)
      | ~ sP0(sK6,X0,sK4)
      | ~ sP2(sK4,sK5) ) ),
    inference(resolution,[],[f148,f92])).

fof(f92,plain,(
    ~ sP1(k2_tarski(sK6,sK6),sK5,sK4) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k2_tarski(sK6,sK6) != X0
      | ~ sP1(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0
          & v4_pre_topc(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v4_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0
        & v4_pre_topc(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v4_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0] :
      ( k2_tarski(sK6,sK6) != X0
      | ~ m1_subset_1(sK9(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(X0,sK5,sK4) ) ),
    inference(subsumption_resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK9(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

% (2235)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f87,plain,(
    ! [X0] :
      ( k2_tarski(sK6,sK6) != X0
      | ~ v4_pre_topc(sK9(X0,sK5,sK4),sK4)
      | ~ m1_subset_1(sK9(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(X0,sK5,sK4) ) ),
    inference(superposition,[],[f67,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k2_tarski(sK6,sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(k2_tarski(X0,X0),X3,X2)
      | ~ r1_tarski(k2_tarski(X0,X0),X3)
      | ~ sP0(X0,X1,X2)
      | ~ sP2(X2,X3) ) ),
    inference(resolution,[],[f132,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | sP1(X3,X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ~ sP1(sK8(X0,X1),X1,X0)
          & r1_tarski(sK8(X0,X1),X1)
          & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP1(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP1(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP1(sK8(X0,X1),X1,X0)
        & r1_tarski(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ sP1(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP1(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ~ sP1(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP1(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f132,plain,(
    ! [X6,X4,X5] :
      ( m1_subset_1(k2_tarski(X6,X6),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ sP0(X6,X5,X4) ) ),
    inference(subsumption_resolution,[],[f128,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2))
        & v3_pre_topc(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,X3)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2))
        & v3_pre_topc(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,X3)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f128,plain,(
    ! [X6,X4,X5] :
      ( m1_subset_1(k2_tarski(X6,X6),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(sK7(X6,X5,X4),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ sP0(X6,X5,X4) ) ),
    inference(superposition,[],[f63,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f119,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl10_2 ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,
    ( ~ r2_hidden(sK6,sK5)
    | spl10_2 ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( ~ r2_hidden(sK6,sK5)
    | ~ r2_hidden(sK6,sK5)
    | spl10_2 ),
    inference(resolution,[],[f114,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f114,plain,
    ( ~ r1_tarski(k2_tarski(sK6,sK6),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (798752768)
% 0.14/0.37  ipcrm: permission denied for id (800489475)
% 0.14/0.38  ipcrm: permission denied for id (800555013)
% 0.14/0.38  ipcrm: permission denied for id (800620551)
% 0.14/0.38  ipcrm: permission denied for id (800686089)
% 0.14/0.38  ipcrm: permission denied for id (798851082)
% 0.14/0.38  ipcrm: permission denied for id (800718859)
% 0.14/0.38  ipcrm: permission denied for id (800751628)
% 0.14/0.39  ipcrm: permission denied for id (798916621)
% 0.14/0.39  ipcrm: permission denied for id (800784398)
% 0.14/0.39  ipcrm: permission denied for id (800817167)
% 0.14/0.39  ipcrm: permission denied for id (800849936)
% 0.21/0.39  ipcrm: permission denied for id (800948243)
% 0.21/0.39  ipcrm: permission denied for id (799014932)
% 0.21/0.40  ipcrm: permission denied for id (799047701)
% 0.21/0.40  ipcrm: permission denied for id (800981014)
% 0.21/0.40  ipcrm: permission denied for id (801013783)
% 0.21/0.40  ipcrm: permission denied for id (801079321)
% 0.21/0.40  ipcrm: permission denied for id (801112090)
% 0.21/0.40  ipcrm: permission denied for id (799113243)
% 0.21/0.40  ipcrm: permission denied for id (799146012)
% 0.21/0.41  ipcrm: permission denied for id (801177630)
% 0.21/0.41  ipcrm: permission denied for id (801275937)
% 0.21/0.41  ipcrm: permission denied for id (801308706)
% 0.21/0.41  ipcrm: permission denied for id (801374244)
% 0.21/0.42  ipcrm: permission denied for id (801407013)
% 0.21/0.42  ipcrm: permission denied for id (799277095)
% 0.21/0.42  ipcrm: permission denied for id (801472552)
% 0.21/0.42  ipcrm: permission denied for id (799375402)
% 0.21/0.42  ipcrm: permission denied for id (799440940)
% 0.21/0.43  ipcrm: permission denied for id (801570861)
% 0.21/0.43  ipcrm: permission denied for id (799473710)
% 0.21/0.43  ipcrm: permission denied for id (801603631)
% 0.21/0.43  ipcrm: permission denied for id (799539249)
% 0.21/0.43  ipcrm: permission denied for id (799572018)
% 0.21/0.44  ipcrm: permission denied for id (801767478)
% 0.21/0.44  ipcrm: permission denied for id (801833016)
% 0.21/0.44  ipcrm: permission denied for id (801865785)
% 0.21/0.44  ipcrm: permission denied for id (799637562)
% 0.21/0.44  ipcrm: permission denied for id (801898555)
% 0.21/0.44  ipcrm: permission denied for id (801931324)
% 0.21/0.45  ipcrm: permission denied for id (799670333)
% 0.21/0.45  ipcrm: permission denied for id (799703102)
% 0.21/0.45  ipcrm: permission denied for id (799735872)
% 0.21/0.45  ipcrm: permission denied for id (801996865)
% 0.21/0.45  ipcrm: permission denied for id (802062403)
% 0.21/0.46  ipcrm: permission denied for id (802127941)
% 0.21/0.46  ipcrm: permission denied for id (802160710)
% 0.21/0.46  ipcrm: permission denied for id (802193479)
% 0.21/0.46  ipcrm: permission denied for id (802226248)
% 0.21/0.47  ipcrm: permission denied for id (802422861)
% 0.21/0.47  ipcrm: permission denied for id (802455630)
% 0.21/0.47  ipcrm: permission denied for id (802553937)
% 0.21/0.47  ipcrm: permission denied for id (799866962)
% 0.21/0.47  ipcrm: permission denied for id (802586707)
% 0.21/0.47  ipcrm: permission denied for id (802619476)
% 0.21/0.47  ipcrm: permission denied for id (802652245)
% 0.21/0.48  ipcrm: permission denied for id (802685014)
% 0.21/0.48  ipcrm: permission denied for id (802717783)
% 0.21/0.48  ipcrm: permission denied for id (802750552)
% 0.21/0.48  ipcrm: permission denied for id (802783321)
% 0.21/0.48  ipcrm: permission denied for id (799965275)
% 0.21/0.48  ipcrm: permission denied for id (802848860)
% 0.21/0.49  ipcrm: permission denied for id (800030815)
% 0.21/0.49  ipcrm: permission denied for id (802947168)
% 0.21/0.49  ipcrm: permission denied for id (800096354)
% 0.21/0.49  ipcrm: permission denied for id (803012707)
% 0.21/0.49  ipcrm: permission denied for id (803078244)
% 0.21/0.50  ipcrm: permission denied for id (803111013)
% 0.21/0.50  ipcrm: permission denied for id (803143782)
% 0.21/0.50  ipcrm: permission denied for id (803242089)
% 0.21/0.50  ipcrm: permission denied for id (803274858)
% 0.21/0.50  ipcrm: permission denied for id (800227435)
% 0.21/0.50  ipcrm: permission denied for id (803340397)
% 0.21/0.51  ipcrm: permission denied for id (803405935)
% 0.21/0.51  ipcrm: permission denied for id (803537010)
% 0.21/0.51  ipcrm: permission denied for id (803569779)
% 0.21/0.51  ipcrm: permission denied for id (803635317)
% 0.34/0.52  ipcrm: permission denied for id (803700855)
% 0.34/0.52  ipcrm: permission denied for id (803766393)
% 0.34/0.52  ipcrm: permission denied for id (803831931)
% 0.34/0.52  ipcrm: permission denied for id (803897469)
% 0.34/0.53  ipcrm: permission denied for id (800391294)
% 0.34/0.53  ipcrm: permission denied for id (803930239)
% 0.37/0.67  % (2240)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.37/0.68  % (2263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.37/0.69  % (2247)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.37/0.69  % (2252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.37/0.70  % (2244)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.37/0.70  % (2237)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.70  % (2255)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.37/0.70  % (2239)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.37/0.70  % (2265)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.37/0.70  % (2260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.37/0.70  % (2261)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.37/0.70  % (2243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.37/0.71  % (2258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.37/0.71  % (2263)Refutation found. Thanks to Tanya!
% 0.37/0.71  % SZS status Theorem for theBenchmark
% 0.37/0.71  % SZS output start Proof for theBenchmark
% 0.37/0.71  fof(f219,plain,(
% 0.37/0.71    $false),
% 0.37/0.71    inference(avatar_sat_refutation,[],[f119,f212,f218])).
% 0.37/0.71  fof(f218,plain,(
% 0.37/0.71    ~spl10_5),
% 0.37/0.71    inference(avatar_contradiction_clause,[],[f217])).
% 0.37/0.71  fof(f217,plain,(
% 0.37/0.71    $false | ~spl10_5),
% 0.37/0.71    inference(subsumption_resolution,[],[f216,f45])).
% 0.37/0.71  fof(f45,plain,(
% 0.37/0.71    r2_hidden(sK6,sK5)),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f24,plain,(
% 0.37/0.71    ((! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 0.37/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f9,f23,f22,f21])).
% 0.37/0.71  fof(f21,plain,(
% 0.37/0.71    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f22,plain,(
% 0.37/0.71    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f23,plain,(
% 0.37/0.71    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(sK4))) => (! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f9,plain,(
% 0.37/0.71    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.37/0.71    inference(flattening,[],[f8])).
% 0.37/0.71  fof(f8,plain,(
% 0.37/0.71    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.37/0.71    inference(ennf_transformation,[],[f7])).
% 0.37/0.71  fof(f7,negated_conjecture,(
% 0.37/0.71    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.37/0.71    inference(negated_conjecture,[],[f6])).
% 0.37/0.71  fof(f6,conjecture,(
% 0.37/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).
% 0.37/0.71  fof(f216,plain,(
% 0.37/0.71    ~r2_hidden(sK6,sK5) | ~spl10_5),
% 0.37/0.71    inference(subsumption_resolution,[],[f214,f44])).
% 0.37/0.71  fof(f44,plain,(
% 0.37/0.71    m1_subset_1(sK6,u1_struct_0(sK4))),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f214,plain,(
% 0.37/0.71    ~m1_subset_1(sK6,u1_struct_0(sK4)) | ~r2_hidden(sK6,sK5) | ~spl10_5),
% 0.37/0.71    inference(resolution,[],[f207,f173])).
% 0.37/0.71  fof(f173,plain,(
% 0.37/0.71    ( ! [X12] : (sP0(X12,sK5,sK4) | ~m1_subset_1(X12,u1_struct_0(sK4)) | ~r2_hidden(X12,sK5)) )),
% 0.37/0.71    inference(subsumption_resolution,[],[f172,f41])).
% 0.37/0.71  fof(f41,plain,(
% 0.37/0.71    l1_pre_topc(sK4)),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f172,plain,(
% 0.37/0.71    ( ! [X12] : (~r2_hidden(X12,sK5) | ~m1_subset_1(X12,u1_struct_0(sK4)) | sP0(X12,sK5,sK4) | ~l1_pre_topc(sK4)) )),
% 0.37/0.71    inference(subsumption_resolution,[],[f168,f43])).
% 0.37/0.71  fof(f43,plain,(
% 0.37/0.71    v2_tex_2(sK5,sK4)),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f168,plain,(
% 0.37/0.71    ( ! [X12] : (~r2_hidden(X12,sK5) | ~m1_subset_1(X12,u1_struct_0(sK4)) | ~v2_tex_2(sK5,sK4) | sP0(X12,sK5,sK4) | ~l1_pre_topc(sK4)) )),
% 0.37/0.71    inference(resolution,[],[f51,f42])).
% 0.37/0.71  fof(f42,plain,(
% 0.37/0.71    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f51,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v2_tex_2(X1,X0) | sP0(X2,X1,X0) | ~l1_pre_topc(X0)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f16])).
% 0.37/0.71  fof(f16,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : (! [X2] : (sP0(X2,X1,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(definition_folding,[],[f11,f15])).
% 0.37/0.71  fof(f15,plain,(
% 0.37/0.71    ! [X2,X1,X0] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0))),
% 0.37/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.37/0.71  fof(f11,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(flattening,[],[f10])).
% 0.37/0.71  fof(f10,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(ennf_transformation,[],[f5])).
% 0.37/0.71  fof(f5,axiom,(
% 0.37/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).
% 0.37/0.71  fof(f207,plain,(
% 0.37/0.71    ( ! [X2] : (~sP0(sK6,X2,sK4)) ) | ~spl10_5),
% 0.37/0.71    inference(avatar_component_clause,[],[f206])).
% 0.37/0.71  fof(f206,plain,(
% 0.37/0.71    spl10_5 <=> ! [X2] : ~sP0(sK6,X2,sK4)),
% 0.37/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.37/0.71  fof(f212,plain,(
% 0.37/0.71    spl10_5 | ~spl10_2),
% 0.37/0.71    inference(avatar_split_clause,[],[f204,f112,f206])).
% 0.37/0.71  fof(f112,plain,(
% 0.37/0.71    spl10_2 <=> r1_tarski(k2_tarski(sK6,sK6),sK5)),
% 0.37/0.71    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.37/0.71  fof(f204,plain,(
% 0.37/0.71    ( ! [X0] : (~sP0(sK6,X0,sK4)) ) | ~spl10_2),
% 0.37/0.71    inference(subsumption_resolution,[],[f203,f75])).
% 0.37/0.71  fof(f75,plain,(
% 0.37/0.71    sP2(sK4,sK5)),
% 0.37/0.71    inference(subsumption_resolution,[],[f74,f43])).
% 0.37/0.71  fof(f74,plain,(
% 0.37/0.71    ~v2_tex_2(sK5,sK4) | sP2(sK4,sK5)),
% 0.37/0.71    inference(resolution,[],[f72,f52])).
% 0.37/0.71  fof(f52,plain,(
% 0.37/0.71    ( ! [X0,X1] : (~sP3(X0,X1) | ~v2_tex_2(X0,X1) | sP2(X1,X0)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f30])).
% 0.37/0.71  fof(f30,plain,(
% 0.37/0.71    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP2(X1,X0)) & (sP2(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP3(X0,X1))),
% 0.37/0.71    inference(rectify,[],[f29])).
% 0.37/0.71  fof(f29,plain,(
% 0.37/0.71    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP2(X0,X1)) & (sP2(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP3(X1,X0))),
% 0.37/0.71    inference(nnf_transformation,[],[f19])).
% 0.37/0.71  fof(f19,plain,(
% 0.37/0.71    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.37/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.37/0.71  fof(f72,plain,(
% 0.37/0.71    sP3(sK5,sK4)),
% 0.37/0.71    inference(subsumption_resolution,[],[f70,f41])).
% 0.37/0.71  fof(f70,plain,(
% 0.37/0.71    sP3(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.37/0.71    inference(resolution,[],[f62,f42])).
% 0.37/0.71  fof(f62,plain,(
% 0.37/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP3(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f20])).
% 0.37/0.71  fof(f20,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : (sP3(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(definition_folding,[],[f13,f19,f18,f17])).
% 0.37/0.71  fof(f17,plain,(
% 0.37/0.71    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.37/0.71  fof(f18,plain,(
% 0.37/0.71    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (sP1(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/0.71    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.37/0.71  fof(f13,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(flattening,[],[f12])).
% 0.37/0.71  fof(f12,plain,(
% 0.37/0.71    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.37/0.71    inference(ennf_transformation,[],[f4])).
% 0.37/0.71  fof(f4,axiom,(
% 0.37/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.37/0.71  fof(f203,plain,(
% 0.37/0.71    ( ! [X0] : (~sP0(sK6,X0,sK4) | ~sP2(sK4,sK5)) ) | ~spl10_2),
% 0.37/0.71    inference(subsumption_resolution,[],[f199,f113])).
% 0.37/0.71  fof(f113,plain,(
% 0.37/0.71    r1_tarski(k2_tarski(sK6,sK6),sK5) | ~spl10_2),
% 0.37/0.71    inference(avatar_component_clause,[],[f112])).
% 0.37/0.71  fof(f199,plain,(
% 0.37/0.71    ( ! [X0] : (~r1_tarski(k2_tarski(sK6,sK6),sK5) | ~sP0(sK6,X0,sK4) | ~sP2(sK4,sK5)) )),
% 0.37/0.71    inference(resolution,[],[f148,f92])).
% 0.37/0.71  fof(f92,plain,(
% 0.37/0.71    ~sP1(k2_tarski(sK6,sK6),sK5,sK4)),
% 0.37/0.71    inference(equality_resolution,[],[f90])).
% 0.37/0.71  fof(f90,plain,(
% 0.37/0.71    ( ! [X0] : (k2_tarski(sK6,sK6) != X0 | ~sP1(X0,sK5,sK4)) )),
% 0.37/0.71    inference(subsumption_resolution,[],[f89,f58])).
% 0.37/0.71  fof(f58,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP1(X0,X1,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f38])).
% 0.37/0.71  fof(f38,plain,(
% 0.37/0.71    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0 & v4_pre_topc(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP1(X0,X1,X2)))),
% 0.37/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f36,f37])).
% 0.37/0.71  fof(f37,plain,(
% 0.37/0.71    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0 & v4_pre_topc(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f36,plain,(
% 0.37/0.71    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP1(X0,X1,X2)))),
% 0.37/0.71    inference(rectify,[],[f35])).
% 0.37/0.71  fof(f35,plain,(
% 0.37/0.71    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X2,X1,X0)))),
% 0.37/0.71    inference(nnf_transformation,[],[f17])).
% 0.37/0.71  fof(f89,plain,(
% 0.37/0.71    ( ! [X0] : (k2_tarski(sK6,sK6) != X0 | ~m1_subset_1(sK9(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(X0,sK5,sK4)) )),
% 0.37/0.71    inference(subsumption_resolution,[],[f87,f59])).
% 0.37/0.71  fof(f59,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (v4_pre_topc(sK9(X0,X1,X2),X2) | ~sP1(X0,X1,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f38])).
% 0.37/0.71  % (2235)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.37/0.71  fof(f87,plain,(
% 0.37/0.71    ( ! [X0] : (k2_tarski(sK6,sK6) != X0 | ~v4_pre_topc(sK9(X0,sK5,sK4),sK4) | ~m1_subset_1(sK9(X0,sK5,sK4),k1_zfmisc_1(u1_struct_0(sK4))) | ~sP1(X0,sK5,sK4)) )),
% 0.37/0.71    inference(superposition,[],[f67,f60])).
% 0.37/0.71  fof(f60,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X2),X1,sK9(X0,X1,X2)) = X0 | ~sP1(X0,X1,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f38])).
% 0.37/0.71  fof(f67,plain,(
% 0.37/0.71    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k2_tarski(sK6,sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.37/0.71    inference(definition_unfolding,[],[f46,f47])).
% 0.37/0.71  fof(f47,plain,(
% 0.37/0.71    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f1])).
% 0.37/0.71  fof(f1,axiom,(
% 0.37/0.71    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.37/0.71  fof(f46,plain,(
% 0.37/0.71    ( ! [X3] : (k9_subset_1(u1_struct_0(sK4),sK5,X3) != k1_tarski(sK6) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 0.37/0.71    inference(cnf_transformation,[],[f24])).
% 0.37/0.71  fof(f148,plain,(
% 0.37/0.71    ( ! [X2,X0,X3,X1] : (sP1(k2_tarski(X0,X0),X3,X2) | ~r1_tarski(k2_tarski(X0,X0),X3) | ~sP0(X0,X1,X2) | ~sP2(X2,X3)) )),
% 0.37/0.71    inference(resolution,[],[f132,f54])).
% 0.37/0.71  fof(f54,plain,(
% 0.37/0.71    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | sP1(X3,X1,X0) | ~sP2(X0,X1)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f34])).
% 0.37/0.71  fof(f34,plain,(
% 0.37/0.71    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(sK8(X0,X1),X1,X0) & r1_tarski(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP1(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1)))),
% 0.37/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 0.37/0.71  fof(f33,plain,(
% 0.37/0.71    ! [X1,X0] : (? [X2] : (~sP1(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP1(sK8(X0,X1),X1,X0) & r1_tarski(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f32,plain,(
% 0.37/0.71    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP1(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1)))),
% 0.37/0.71    inference(rectify,[],[f31])).
% 0.37/0.71  fof(f31,plain,(
% 0.37/0.71    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : (~sP1(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP1(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1)))),
% 0.37/0.71    inference(nnf_transformation,[],[f18])).
% 0.37/0.71  fof(f132,plain,(
% 0.37/0.71    ( ! [X6,X4,X5] : (m1_subset_1(k2_tarski(X6,X6),k1_zfmisc_1(u1_struct_0(X4))) | ~sP0(X6,X5,X4)) )),
% 0.37/0.71    inference(subsumption_resolution,[],[f128,f48])).
% 0.37/0.71  fof(f48,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f28])).
% 0.37/0.71  fof(f28,plain,(
% 0.37/0.71    ! [X0,X1,X2] : ((k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2)) & v3_pre_topc(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2))),
% 0.37/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f27])).
% 0.37/0.71  fof(f27,plain,(
% 0.37/0.71    ! [X2,X1,X0] : (? [X3] : (k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2)) & v3_pre_topc(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.37/0.71    introduced(choice_axiom,[])).
% 0.37/0.71  fof(f26,plain,(
% 0.37/0.71    ! [X0,X1,X2] : (? [X3] : (k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2))),
% 0.37/0.71    inference(rectify,[],[f25])).
% 0.37/0.71  fof(f25,plain,(
% 0.37/0.71    ! [X2,X1,X0] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0))),
% 0.37/0.71    inference(nnf_transformation,[],[f15])).
% 0.37/0.71  fof(f128,plain,(
% 0.37/0.71    ( ! [X6,X4,X5] : (m1_subset_1(k2_tarski(X6,X6),k1_zfmisc_1(u1_struct_0(X4))) | ~m1_subset_1(sK7(X6,X5,X4),k1_zfmisc_1(u1_struct_0(X4))) | ~sP0(X6,X5,X4)) )),
% 0.37/0.71    inference(superposition,[],[f63,f68])).
% 0.37/0.71  fof(f68,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.37/0.71    inference(definition_unfolding,[],[f50,f47])).
% 0.37/0.71  fof(f50,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (k1_tarski(X0) = k9_subset_1(u1_struct_0(X2),X1,sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f28])).
% 0.37/0.71  fof(f63,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.37/0.71    inference(cnf_transformation,[],[f14])).
% 0.37/0.71  fof(f14,plain,(
% 0.37/0.71    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.37/0.71    inference(ennf_transformation,[],[f3])).
% 0.37/0.71  fof(f3,axiom,(
% 0.37/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.37/0.71  fof(f119,plain,(
% 0.37/0.71    spl10_2),
% 0.37/0.71    inference(avatar_contradiction_clause,[],[f118])).
% 0.37/0.71  fof(f118,plain,(
% 0.37/0.71    $false | spl10_2),
% 0.37/0.71    inference(subsumption_resolution,[],[f117,f45])).
% 0.37/0.71  fof(f117,plain,(
% 0.37/0.71    ~r2_hidden(sK6,sK5) | spl10_2),
% 0.37/0.71    inference(duplicate_literal_removal,[],[f116])).
% 0.37/0.71  fof(f116,plain,(
% 0.37/0.71    ~r2_hidden(sK6,sK5) | ~r2_hidden(sK6,sK5) | spl10_2),
% 0.37/0.71    inference(resolution,[],[f114,f66])).
% 0.37/0.71  fof(f66,plain,(
% 0.37/0.71    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.37/0.71    inference(cnf_transformation,[],[f40])).
% 0.37/0.71  fof(f40,plain,(
% 0.37/0.71    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.37/0.71    inference(flattening,[],[f39])).
% 0.37/0.71  fof(f39,plain,(
% 0.37/0.71    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.37/0.71    inference(nnf_transformation,[],[f2])).
% 0.37/0.71  fof(f2,axiom,(
% 0.37/0.71    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.37/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.37/0.71  fof(f114,plain,(
% 0.37/0.71    ~r1_tarski(k2_tarski(sK6,sK6),sK5) | spl10_2),
% 0.37/0.71    inference(avatar_component_clause,[],[f112])).
% 0.37/0.71  % SZS output end Proof for theBenchmark
% 0.37/0.71  % (2263)------------------------------
% 0.37/0.71  % (2263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.71  % (2263)Termination reason: Refutation
% 0.37/0.71  
% 0.37/0.71  % (2263)Memory used [KB]: 6396
% 0.37/0.71  % (2263)Time elapsed: 0.146 s
% 0.37/0.71  % (2263)------------------------------
% 0.37/0.71  % (2263)------------------------------
% 0.37/0.71  % (2236)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.37/0.71  % (2080)Success in time 0.344 s
%------------------------------------------------------------------------------

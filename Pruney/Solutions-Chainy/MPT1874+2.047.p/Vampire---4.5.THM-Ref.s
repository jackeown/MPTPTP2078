%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:28 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 249 expanded)
%              Number of leaves         :   17 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  375 (1475 expanded)
%              Number of equality atoms :   44 ( 199 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f100,f120,f194,f202])).

fof(f202,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f196,f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f196,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f194,plain,
    ( spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f188,f40])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f183,f43])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f180,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0) )
    | spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f179,f73])).

fof(f73,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ r2_hidden(X5,X4) ) ),
    inference(subsumption_resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f63,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ r2_hidden(X5,X4) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tarski(X0) = k6_domain_1(X1,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f51,f58])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f179,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f178,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( k1_tarski(sK2) != k1_tarski(sK2)
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1)
    | spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f71,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))
        | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f99,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3)))
        | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_6
  <=> ! [X3] :
        ( k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3)))
        | ~ m1_subset_1(X3,sK1)
        | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f71,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_2
  <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f115,f43])).

fof(f115,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f112,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X5,X4) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_5
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(sK1,sK1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X1,sK1),sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f102,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f100,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f85,f98,f95])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3)))
      | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ r2_hidden(X5,X4) ) ),
    inference(resolution,[],[f80,f73])).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f72,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f64,f69,f66])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f44,f60])).

fof(f44,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (27060)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.49  % (27052)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (27048)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (27056)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (27047)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (27045)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (27047)Refutation not found, incomplete strategy% (27047)------------------------------
% 1.27/0.53  % (27047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (27047)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (27047)Memory used [KB]: 10874
% 1.27/0.53  % (27047)Time elapsed: 0.115 s
% 1.27/0.53  % (27047)------------------------------
% 1.27/0.53  % (27047)------------------------------
% 1.27/0.53  % (27057)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (27066)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.53  % (27050)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  % (27062)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.54  % (27067)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.54  % (27063)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.54  % (27065)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.54  % (27046)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (27059)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (27049)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (27054)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.54  % (27061)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.55  % (27074)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.55  % (27071)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.55  % (27067)Refutation not found, incomplete strategy% (27067)------------------------------
% 1.27/0.55  % (27067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (27067)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (27067)Memory used [KB]: 10746
% 1.27/0.55  % (27067)Time elapsed: 0.092 s
% 1.27/0.55  % (27067)------------------------------
% 1.27/0.55  % (27067)------------------------------
% 1.27/0.55  % (27068)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.55  % (27051)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.55  % (27055)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.55  % (27058)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.55  % (27053)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.55  % (27070)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.55  % (27048)Refutation found. Thanks to Tanya!
% 1.27/0.55  % SZS status Theorem for theBenchmark
% 1.27/0.55  % SZS output start Proof for theBenchmark
% 1.27/0.55  fof(f204,plain,(
% 1.27/0.55    $false),
% 1.27/0.55    inference(avatar_sat_refutation,[],[f72,f100,f120,f194,f202])).
% 1.27/0.55  fof(f202,plain,(
% 1.27/0.55    ~spl5_1),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f201])).
% 1.27/0.55  fof(f201,plain,(
% 1.27/0.55    $false | ~spl5_1),
% 1.27/0.55    inference(subsumption_resolution,[],[f196,f40])).
% 1.27/0.55  fof(f40,plain,(
% 1.27/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f27,plain,(
% 1.27/0.55    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.27/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f26,f25,f24])).
% 1.27/0.55  fof(f24,plain,(
% 1.27/0.55    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.27/0.55    introduced(choice_axiom,[])).
% 1.27/0.55  fof(f25,plain,(
% 1.27/0.55    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.27/0.55    introduced(choice_axiom,[])).
% 1.27/0.55  fof(f26,plain,(
% 1.27/0.55    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.27/0.55    introduced(choice_axiom,[])).
% 1.27/0.55  fof(f12,plain,(
% 1.27/0.55    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.55    inference(flattening,[],[f11])).
% 1.27/0.55  fof(f11,plain,(
% 1.27/0.55    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.55    inference(ennf_transformation,[],[f10])).
% 1.27/0.55  fof(f10,negated_conjecture,(
% 1.27/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.27/0.55    inference(negated_conjecture,[],[f9])).
% 1.27/0.55  fof(f9,conjecture,(
% 1.27/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 1.27/0.55  fof(f196,plain,(
% 1.27/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_1),
% 1.27/0.55    inference(resolution,[],[f67,f43])).
% 1.27/0.55  fof(f43,plain,(
% 1.27/0.55    r2_hidden(sK2,sK1)),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f67,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_1),
% 1.27/0.55    inference(avatar_component_clause,[],[f66])).
% 1.27/0.55  fof(f66,plain,(
% 1.27/0.55    spl5_1 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0))),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.27/0.55  fof(f194,plain,(
% 1.27/0.55    spl5_2 | ~spl5_6),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f193])).
% 1.27/0.55  fof(f193,plain,(
% 1.27/0.55    $false | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(subsumption_resolution,[],[f188,f40])).
% 1.27/0.55  fof(f188,plain,(
% 1.27/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(resolution,[],[f183,f43])).
% 1.27/0.55  fof(f183,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(subsumption_resolution,[],[f180,f42])).
% 1.27/0.55  fof(f42,plain,(
% 1.27/0.55    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f180,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) ) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(resolution,[],[f179,f73])).
% 1.27/0.55  fof(f73,plain,(
% 1.27/0.55    ( ! [X4,X2,X5,X3] : (m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~r2_hidden(X5,X4)) )),
% 1.27/0.55    inference(subsumption_resolution,[],[f63,f58])).
% 1.27/0.55  fof(f58,plain,(
% 1.27/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f23])).
% 1.27/0.55  fof(f23,plain,(
% 1.27/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.27/0.55    inference(ennf_transformation,[],[f5])).
% 1.27/0.55  fof(f5,axiom,(
% 1.27/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.27/0.55  fof(f63,plain,(
% 1.27/0.55    ( ! [X4,X2,X5,X3] : (m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,X2) | v1_xboole_0(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~r2_hidden(X5,X4)) )),
% 1.27/0.55    inference(duplicate_literal_removal,[],[f62])).
% 1.27/0.55  fof(f62,plain,(
% 1.27/0.55    ( ! [X4,X2,X5,X3] : (m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,X2) | v1_xboole_0(X2) | ~m1_subset_1(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~r2_hidden(X5,X4)) )),
% 1.27/0.55    inference(superposition,[],[f52,f60])).
% 1.27/0.55  fof(f60,plain,(
% 1.27/0.55    ( ! [X2,X0,X3,X1] : (k1_tarski(X0) = k6_domain_1(X1,X0) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(X3,X2)) )),
% 1.27/0.55    inference(resolution,[],[f51,f58])).
% 1.27/0.55  fof(f51,plain,(
% 1.27/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f19])).
% 1.27/0.55  fof(f19,plain,(
% 1.27/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.27/0.55    inference(flattening,[],[f18])).
% 1.27/0.55  fof(f18,plain,(
% 1.27/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.27/0.55    inference(ennf_transformation,[],[f7])).
% 1.27/0.55  fof(f7,axiom,(
% 1.27/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.27/0.55  fof(f52,plain,(
% 1.27/0.55    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f21])).
% 1.27/0.55  fof(f21,plain,(
% 1.27/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.27/0.55    inference(flattening,[],[f20])).
% 1.27/0.55  fof(f20,plain,(
% 1.27/0.55    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.27/0.55    inference(ennf_transformation,[],[f6])).
% 1.27/0.55  fof(f6,axiom,(
% 1.27/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.27/0.55  fof(f179,plain,(
% 1.27/0.55    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(subsumption_resolution,[],[f178,f43])).
% 1.27/0.55  fof(f178,plain,(
% 1.27/0.55    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(trivial_inequality_removal,[],[f177])).
% 1.27/0.55  fof(f177,plain,(
% 1.27/0.55    k1_tarski(sK2) != k1_tarski(sK2) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1) | (spl5_2 | ~spl5_6)),
% 1.27/0.55    inference(superposition,[],[f71,f173])).
% 1.27/0.55  fof(f173,plain,(
% 1.27/0.55    ( ! [X0] : (k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1)) ) | ~spl5_6),
% 1.27/0.55    inference(resolution,[],[f99,f49])).
% 1.27/0.55  fof(f49,plain,(
% 1.27/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f15])).
% 1.27/0.55  fof(f15,plain,(
% 1.27/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.27/0.55    inference(ennf_transformation,[],[f2])).
% 1.27/0.55  fof(f2,axiom,(
% 1.27/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.27/0.55  fof(f99,plain,(
% 1.27/0.55    ( ! [X3] : (~m1_subset_1(X3,sK1) | k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3))) | ~m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_6),
% 1.27/0.55    inference(avatar_component_clause,[],[f98])).
% 1.27/0.55  fof(f98,plain,(
% 1.27/0.55    spl5_6 <=> ! [X3] : (k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3))) | ~m1_subset_1(X3,sK1) | ~m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.27/0.55  fof(f71,plain,(
% 1.27/0.55    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | spl5_2),
% 1.27/0.55    inference(avatar_component_clause,[],[f69])).
% 1.27/0.55  fof(f69,plain,(
% 1.27/0.55    spl5_2 <=> k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.27/0.55  fof(f120,plain,(
% 1.27/0.55    ~spl5_5),
% 1.27/0.55    inference(avatar_contradiction_clause,[],[f116])).
% 1.27/0.55  fof(f116,plain,(
% 1.27/0.55    $false | ~spl5_5),
% 1.27/0.55    inference(resolution,[],[f115,f43])).
% 1.27/0.55  fof(f115,plain,(
% 1.27/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl5_5),
% 1.27/0.55    inference(subsumption_resolution,[],[f112,f102])).
% 1.27/0.55  fof(f102,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | ~r2_hidden(X0,X1)) ) | ~spl5_5),
% 1.27/0.55    inference(resolution,[],[f96,f57])).
% 1.27/0.55  fof(f57,plain,(
% 1.27/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f36])).
% 1.27/0.55  fof(f36,plain,(
% 1.27/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.27/0.55    inference(nnf_transformation,[],[f4])).
% 1.27/0.55  fof(f4,axiom,(
% 1.27/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.27/0.55  fof(f96,plain,(
% 1.27/0.55    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~r2_hidden(X5,X4)) ) | ~spl5_5),
% 1.27/0.55    inference(avatar_component_clause,[],[f95])).
% 1.27/0.55  fof(f95,plain,(
% 1.27/0.55    spl5_5 <=> ! [X5,X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~r2_hidden(X5,X4))),
% 1.27/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.27/0.55  fof(f112,plain,(
% 1.27/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK1,sK1)) ) | ~spl5_5),
% 1.27/0.55    inference(resolution,[],[f106,f54])).
% 1.27/0.55  fof(f54,plain,(
% 1.27/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f35])).
% 1.27/0.55  fof(f35,plain,(
% 1.27/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.27/0.55  fof(f34,plain,(
% 1.27/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.27/0.55    introduced(choice_axiom,[])).
% 1.27/0.55  fof(f33,plain,(
% 1.27/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.55    inference(rectify,[],[f32])).
% 1.27/0.55  fof(f32,plain,(
% 1.27/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.27/0.55    inference(nnf_transformation,[],[f22])).
% 1.27/0.55  fof(f22,plain,(
% 1.27/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.27/0.55    inference(ennf_transformation,[],[f1])).
% 1.27/0.55  fof(f1,axiom,(
% 1.27/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.27/0.55  fof(f106,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X1,sK1),sK1) | ~r2_hidden(X0,X1)) ) | ~spl5_5),
% 1.27/0.55    inference(resolution,[],[f102,f55])).
% 1.27/0.55  fof(f55,plain,(
% 1.27/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f35])).
% 1.27/0.55  fof(f100,plain,(
% 1.27/0.55    spl5_5 | spl5_6),
% 1.27/0.55    inference(avatar_split_clause,[],[f85,f98,f95])).
% 1.27/0.55  fof(f85,plain,(
% 1.27/0.55    ( ! [X4,X5,X3] : (k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3))) | ~m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,sK1) | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~r2_hidden(X5,X4)) )),
% 1.27/0.55    inference(resolution,[],[f80,f73])).
% 1.27/0.55  fof(f80,plain,(
% 1.27/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.27/0.55    inference(resolution,[],[f78,f56])).
% 1.27/0.55  fof(f56,plain,(
% 1.27/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.27/0.55    inference(cnf_transformation,[],[f36])).
% 1.27/0.55  fof(f78,plain,(
% 1.27/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.27/0.55    inference(subsumption_resolution,[],[f77,f40])).
% 1.27/0.55  fof(f77,plain,(
% 1.27/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.27/0.55    inference(resolution,[],[f76,f41])).
% 1.27/0.55  fof(f41,plain,(
% 1.27/0.55    v2_tex_2(sK1,sK0)),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f76,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.27/0.55    inference(subsumption_resolution,[],[f75,f37])).
% 1.27/0.55  fof(f37,plain,(
% 1.27/0.55    ~v2_struct_0(sK0)),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f75,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.27/0.55    inference(subsumption_resolution,[],[f74,f38])).
% 1.27/0.55  fof(f38,plain,(
% 1.27/0.55    v2_pre_topc(sK0)),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f74,plain,(
% 1.27/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.27/0.55    inference(resolution,[],[f45,f39])).
% 1.27/0.55  fof(f39,plain,(
% 1.27/0.55    l1_pre_topc(sK0)),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  fof(f45,plain,(
% 1.27/0.55    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/0.55    inference(cnf_transformation,[],[f31])).
% 1.27/0.55  fof(f31,plain,(
% 1.27/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.27/0.55  fof(f30,plain,(
% 1.27/0.55    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.27/0.55    introduced(choice_axiom,[])).
% 1.27/0.55  fof(f29,plain,(
% 1.27/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.55    inference(rectify,[],[f28])).
% 1.27/0.55  fof(f28,plain,(
% 1.27/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.55    inference(nnf_transformation,[],[f14])).
% 1.27/0.55  fof(f14,plain,(
% 1.27/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/0.55    inference(flattening,[],[f13])).
% 1.27/0.55  fof(f13,plain,(
% 1.27/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/0.55    inference(ennf_transformation,[],[f8])).
% 1.27/0.55  fof(f8,axiom,(
% 1.27/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.27/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 1.27/0.55  fof(f72,plain,(
% 1.27/0.55    spl5_1 | ~spl5_2),
% 1.27/0.55    inference(avatar_split_clause,[],[f64,f69,f66])).
% 1.27/0.55  fof(f64,plain,(
% 1.27/0.55    ( ! [X0,X1] : (k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 1.27/0.55    inference(subsumption_resolution,[],[f61,f42])).
% 1.27/0.55  fof(f61,plain,(
% 1.27/0.55    ( ! [X0,X1] : (k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 1.27/0.55    inference(superposition,[],[f44,f60])).
% 1.27/0.55  fof(f44,plain,(
% 1.27/0.55    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.27/0.55    inference(cnf_transformation,[],[f27])).
% 1.27/0.55  % SZS output end Proof for theBenchmark
% 1.27/0.55  % (27048)------------------------------
% 1.27/0.55  % (27048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (27048)Termination reason: Refutation
% 1.27/0.55  
% 1.27/0.55  % (27048)Memory used [KB]: 10874
% 1.27/0.55  % (27048)Time elapsed: 0.140 s
% 1.27/0.55  % (27048)------------------------------
% 1.27/0.55  % (27048)------------------------------
% 1.27/0.55  % (27044)Success in time 0.188 s
%------------------------------------------------------------------------------

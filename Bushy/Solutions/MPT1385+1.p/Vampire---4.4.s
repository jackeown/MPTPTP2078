%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t10_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 407 expanded)
%              Number of leaves         :   40 ( 156 expanded)
%              Depth                    :   12
%              Number of atoms          :  587 (2255 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f155,f173,f215,f217,f220,f222,f224,f228,f466,f581,f724,f728,f1314,f1875,f1890,f1961,f2972,f2979,f2981,f2983,f2987,f3309])).

fof(f3309,plain,
    ( ~ spl10_13
    | ~ spl10_15
    | ~ spl10_39
    | ~ spl10_19
    | spl10_112
    | ~ spl10_96 ),
    inference(avatar_split_clause,[],[f3306,f557,f623,f301,f2133,f179,f176])).

fof(f176,plain,
    ( spl10_13
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f179,plain,
    ( spl10_15
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f2133,plain,
    ( spl10_39
  <=> ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f301,plain,
    ( spl10_19
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f623,plain,
    ( spl10_112
  <=> m2_connsp_2(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_112])])).

fof(f557,plain,
    ( spl10_96
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f3306,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_96 ),
    inference(resolution,[],[f3299,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',d2_connsp_2)).

fof(f3299,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ spl10_96 ),
    inference(resolution,[],[f558,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',t3_subset)).

fof(f558,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f557])).

fof(f2987,plain,
    ( ~ spl10_17
    | spl10_70
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f2985,f153,f450,f182])).

fof(f182,plain,
    ( spl10_17
  <=> ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f450,plain,
    ( spl10_70
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f153,plain,
    ( spl10_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2985,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(resolution,[],[f154,f199])).

fof(f199,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK2,sK0,X2)
      | r2_hidden(X2,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f98,f99,f100,f191])).

fof(f191,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK2,sK0,X2)
      | r2_hidden(X2,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f102,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',d1_connsp_2)).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f72,f75,f74,f73])).

fof(f73,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK0,X1)
                | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & ( m1_connsp_2(X2,sK0,X1)
                | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,X0,sK1)
              | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1)) )
            & ( m1_connsp_2(X2,X0,sK1)
              | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),sK1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,X0,X1)
            | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & ( m1_connsp_2(X2,X0,X1)
            | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_connsp_2(sK2,X0,X1)
          | ~ m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & ( m1_connsp_2(sK2,X0,X1)
          | m2_connsp_2(sK2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',t10_connsp_2)).

fof(f100,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f99,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f98,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f154,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2983,plain,
    ( spl10_72
    | ~ spl10_95
    | spl10_96
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f2753,f464,f557,f554,f461])).

fof(f461,plain,
    ( spl10_72
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f554,plain,
    ( spl10_95
  <=> ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f464,plain,
    ( spl10_74
  <=> k6_domain_1(k1_tops_1(sK0,sK2),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f2753,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl10_74 ),
    inference(superposition,[],[f117,f465])).

fof(f465,plain,
    ( k6_domain_1(k1_tops_1(sK0,sK2),sK1) = k1_tarski(sK1)
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f464])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',dt_k6_domain_1)).

fof(f2981,plain,
    ( ~ spl10_13
    | ~ spl10_15
    | ~ spl10_39
    | ~ spl10_19
    | spl10_112
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1502,f734,f623,f301,f2133,f179,f176])).

fof(f734,plain,
    ( spl10_140
  <=> r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f1502,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_140 ),
    inference(resolution,[],[f735,f111])).

fof(f735,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ spl10_140 ),
    inference(avatar_component_clause,[],[f734])).

fof(f2979,plain,(
    spl10_19 ),
    inference(avatar_contradiction_clause,[],[f2977])).

fof(f2977,plain,
    ( $false
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f102,f302])).

fof(f302,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f301])).

fof(f2972,plain,
    ( spl10_2
    | ~ spl10_17
    | ~ spl10_414 ),
    inference(avatar_split_clause,[],[f2969,f1959,f182,f153])).

fof(f1959,plain,
    ( spl10_414
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_414])])).

fof(f2969,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl10_414 ),
    inference(resolution,[],[f1960,f140])).

fof(f140,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f90,f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',d1_tarski)).

fof(f1960,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK2,sK0,X0) )
    | ~ spl10_414 ),
    inference(avatar_component_clause,[],[f1959])).

fof(f1961,plain,
    ( spl10_8
    | ~ spl10_13
    | ~ spl10_15
    | ~ spl10_19
    | spl10_414
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1951,f734,f1959,f301,f179,f176,f168])).

fof(f168,plain,
    ( spl10_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1951,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | m1_connsp_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_140 ),
    inference(resolution,[],[f1504,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1504,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ r2_hidden(X0,k1_tarski(sK1)) )
    | ~ spl10_140 ),
    inference(resolution,[],[f735,f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f86,f87])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',d3_tarski)).

fof(f1890,plain,
    ( ~ spl10_113
    | spl10_140
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f1878,f285,f734,f1266])).

fof(f1266,plain,
    ( spl10_113
  <=> ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f285,plain,
    ( spl10_38
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f1878,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl10_38 ),
    inference(resolution,[],[f286,f198])).

fof(f198,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k1_tops_1(sK0,sK2))
      | ~ m2_connsp_2(sK2,sK0,X1) ) ),
    inference(global_subsumption,[],[f99,f100,f190])).

fof(f190,plain,(
    ! [X1] :
      ( ~ m2_connsp_2(sK2,sK0,X1)
      | r1_tarski(X1,k1_tops_1(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f102,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f286,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f285])).

fof(f1875,plain,
    ( spl10_4
    | ~ spl10_17
    | spl10_38
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f1864,f161,f285,f182,f158])).

fof(f158,plain,
    ( spl10_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f161,plain,
    ( spl10_6
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1864,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(superposition,[],[f117,f162])).

fof(f162,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1314,plain,
    ( ~ spl10_0
    | ~ spl10_6
    | spl10_113 ),
    inference(avatar_contradiction_clause,[],[f1313])).

fof(f1313,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_6
    | ~ spl10_113 ),
    inference(subsumption_resolution,[],[f729,f1267])).

fof(f1267,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl10_113 ),
    inference(avatar_component_clause,[],[f1266])).

fof(f729,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl10_0
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f151,f162])).

fof(f151,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_0
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f728,plain,
    ( ~ spl10_70
    | ~ spl10_72 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f454,f462])).

fof(f462,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f461])).

fof(f454,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl10_70 ),
    inference(resolution,[],[f451,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',t7_boole)).

fof(f451,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f450])).

fof(f724,plain,
    ( spl10_1
    | ~ spl10_6
    | ~ spl10_112 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_112 ),
    inference(subsumption_resolution,[],[f282,f624])).

fof(f624,plain,
    ( m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl10_112 ),
    inference(avatar_component_clause,[],[f623])).

fof(f282,plain,
    ( ~ m2_connsp_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f162,f144])).

fof(f144,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl10_1
  <=> ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f581,plain,
    ( ~ spl10_70
    | spl10_95 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl10_70
    | ~ spl10_95 ),
    inference(subsumption_resolution,[],[f455,f555])).

fof(f555,plain,
    ( ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_95 ),
    inference(avatar_component_clause,[],[f554])).

fof(f455,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl10_70 ),
    inference(resolution,[],[f451,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',t1_subset)).

fof(f466,plain,
    ( spl10_72
    | spl10_74
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f459,f450,f464,f461])).

fof(f459,plain,
    ( k6_domain_1(k1_tops_1(sK0,sK2),sK1) = k1_tarski(sK1)
    | v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl10_70 ),
    inference(resolution,[],[f455,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',redefinition_k6_domain_1)).

fof(f228,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f100,f218])).

fof(f218,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_11 ),
    inference(resolution,[],[f172,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',dt_l1_pre_topc)).

fof(f172,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl10_11
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f224,plain,(
    ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f98,f169])).

fof(f169,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f222,plain,
    ( spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f221,f161,f158])).

fof(f221,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f101,f116])).

fof(f101,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f220,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f101,f183])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f217,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f100,f180])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f215,plain,(
    spl10_13 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f99,f177])).

fof(f177,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f173,plain,
    ( spl10_8
    | ~ spl10_11
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f164,f158,f171,f168])).

fof(f164,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4 ),
    inference(resolution,[],[f159,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t10_connsp_2.p',fc2_struct_0)).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f155,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f103,f153,f150])).

fof(f103,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f76])).

fof(f148,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f104,f146,f143])).

fof(f146,plain,
    ( spl10_3
  <=> ~ m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f104,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------

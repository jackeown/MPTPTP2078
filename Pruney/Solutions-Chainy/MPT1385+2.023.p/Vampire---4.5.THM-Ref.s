%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 429 expanded)
%              Number of leaves         :   37 ( 171 expanded)
%              Depth                    :   11
%              Number of atoms          :  635 (2426 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f81,f92,f111,f132,f134,f136,f152,f154,f156,f175,f189,f206,f221,f231,f234,f267,f273,f281,f289,f305,f309,f321,f330])).

fof(f330,plain,
    ( spl4_1
    | ~ spl4_7
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl4_1
    | ~ spl4_7
    | ~ spl4_33 ),
    inference(resolution,[],[f288,f112])).

fof(f112,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | spl4_1
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f74,f110])).

fof(f110,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_7
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f74,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f288,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl4_33
  <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f321,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_19
    | spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f311,f228,f77,f184,f145,f141,f126,f122])).

fof(f122,plain,
    ( spl4_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f126,plain,
    ( spl4_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( spl4_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f145,plain,
    ( spl4_13
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f184,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f77,plain,
    ( spl4_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f228,plain,
    ( spl4_27
  <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f311,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_27 ),
    inference(resolution,[],[f300,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f300,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl4_27 ),
    inference(resolution,[],[f230,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

% (3779)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f230,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f309,plain,
    ( ~ spl4_4
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(resolution,[],[f295,f205])).

fof(f205,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_22
  <=> r2_hidden(sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f295,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK3(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f290,f151])).

fof(f151,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_14
  <=> m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f91,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f305,plain,
    ( ~ spl4_27
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl4_27
    | spl4_32 ),
    inference(resolution,[],[f300,f279])).

fof(f279,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl4_32
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f289,plain,
    ( spl4_33
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_30
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f282,f278,f265,f224,f184,f286])).

fof(f224,plain,
    ( spl4_26
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f265,plain,
    ( spl4_30
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f282,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl4_30
    | ~ spl4_32 ),
    inference(resolution,[],[f280,f268])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X0,sK0,k2_tarski(X1,X1)) )
    | ~ spl4_30 ),
    inference(resolution,[],[f266,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f53])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f265])).

fof(f280,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f281,plain,
    ( ~ spl4_19
    | spl4_32
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f276,f271,f77,f278,f184])).

fof(f271,plain,
    ( spl4_31
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f276,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(resolution,[],[f274,f79])).

fof(f79,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f274,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_31 ),
    inference(resolution,[],[f272,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

% (3777)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f40,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK0,X1)
              | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & ( m1_connsp_2(X2,sK0,X1)
              | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK0,sK1)
            | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & ( m1_connsp_2(X2,sK0,sK1)
            | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK0,sK1)
          | ~ m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & ( m1_connsp_2(X2,sK0,sK1)
          | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(sK2,sK0,sK1)
        | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & ( m1_connsp_2(sK2,sK0,sK1)
        | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f273,plain,
    ( spl4_9
    | ~ spl4_10
    | spl4_31 ),
    inference(avatar_split_clause,[],[f269,f271,f126,f122])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f267,plain,
    ( ~ spl4_10
    | spl4_30 ),
    inference(avatar_split_clause,[],[f263,f265,f126])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m2_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f234,plain,
    ( ~ spl4_3
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl4_3
    | spl4_26 ),
    inference(resolution,[],[f232,f87])).

fof(f87,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_3
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f232,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl4_26 ),
    inference(resolution,[],[f226,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f226,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f224])).

fof(f231,plain,
    ( ~ spl4_19
    | ~ spl4_26
    | spl4_27
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f222,f219,f108,f73,f228,f224,f184])).

fof(f219,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | r1_tarski(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f222,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(resolution,[],[f220,f200])).

fof(f200,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f75,f110])).

fof(f75,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | r1_tarski(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f219])).

fof(f221,plain,
    ( ~ spl4_10
    | spl4_25 ),
    inference(avatar_split_clause,[],[f217,f219,f126])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k1_tops_1(sK0,X0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f206,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13
    | spl4_22
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f178,f173,f149,f203,f145,f141,f126,f122])).

fof(f173,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f178,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f176,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK3(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK3(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,X0) )
    | ~ spl4_17 ),
    inference(resolution,[],[f174,f49])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f189,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl4_19 ),
    inference(resolution,[],[f186,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f186,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f184])).

fof(f175,plain,
    ( spl4_9
    | ~ spl4_10
    | spl4_17 ),
    inference(avatar_split_clause,[],[f171,f173,f126,f122])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f156,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f147,f49])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f154,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f143,f48])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f152,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13
    | spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f139,f130,f149,f145,f141,f126,f122])).

fof(f130,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f139,plain,
    ( m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f137,f63])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_11 ),
    inference(resolution,[],[f131,f49])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f136,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_9 ),
    inference(resolution,[],[f124,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f134,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f128,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f128,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f132,plain,
    ( spl4_9
    | ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f120,f130,f126,f122])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f48])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f111,plain,
    ( spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f104,f108,f89])).

fof(f104,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f92,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f82,f89,f85])).

fof(f82,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f49])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f81,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f52,f77,f73])).

fof(f52,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f51,f77,f73])).

fof(f51,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:02:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (3784)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.45  % (3781)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.45  % (3782)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (3778)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (3791)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.46  % (3783)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (3778)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f331,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f80,f81,f92,f111,f132,f134,f136,f152,f154,f156,f175,f189,f206,f221,f231,f234,f267,f273,f281,f289,f305,f309,f321,f330])).
% 0.19/0.46  fof(f330,plain,(
% 0.19/0.46    spl4_1 | ~spl4_7 | ~spl4_33),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f327])).
% 0.19/0.46  fof(f327,plain,(
% 0.19/0.46    $false | (spl4_1 | ~spl4_7 | ~spl4_33)),
% 0.19/0.46    inference(resolution,[],[f288,f112])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (spl4_1 | ~spl4_7)),
% 0.19/0.46    inference(backward_demodulation,[],[f74,f110])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl4_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f108])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    spl4_7 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl4_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f73])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    spl4_1 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.46  fof(f288,plain,(
% 0.19/0.46    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~spl4_33),
% 0.19/0.46    inference(avatar_component_clause,[],[f286])).
% 0.19/0.46  fof(f286,plain,(
% 0.19/0.46    spl4_33 <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.19/0.46  fof(f321,plain,(
% 0.19/0.46    spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13 | ~spl4_19 | spl4_2 | ~spl4_27),
% 0.19/0.46    inference(avatar_split_clause,[],[f311,f228,f77,f184,f145,f141,f126,f122])).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    spl4_9 <=> v2_struct_0(sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.46  fof(f126,plain,(
% 0.19/0.46    spl4_10 <=> v2_pre_topc(sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.46  fof(f141,plain,(
% 0.19/0.46    spl4_12 <=> l1_pre_topc(sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.46  fof(f145,plain,(
% 0.19/0.46    spl4_13 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.46  fof(f184,plain,(
% 0.19/0.46    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    spl4_2 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.46  fof(f228,plain,(
% 0.19/0.46    spl4_27 <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.19/0.46  fof(f311,plain,(
% 0.19/0.46    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_27),
% 0.19/0.46    inference(resolution,[],[f300,f55])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.19/0.46  fof(f300,plain,(
% 0.19/0.46    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl4_27),
% 0.19/0.46    inference(resolution,[],[f230,f71])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f65,f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.19/0.46    inference(nnf_transformation,[],[f2])).
% 0.19/0.46  % (3779)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.19/0.46  fof(f230,plain,(
% 0.19/0.46    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~spl4_27),
% 0.19/0.46    inference(avatar_component_clause,[],[f228])).
% 0.19/0.46  fof(f309,plain,(
% 0.19/0.46    ~spl4_4 | ~spl4_14 | ~spl4_22),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f308])).
% 0.19/0.46  fof(f308,plain,(
% 0.19/0.46    $false | (~spl4_4 | ~spl4_14 | ~spl4_22)),
% 0.19/0.46    inference(resolution,[],[f295,f205])).
% 0.19/0.46  fof(f205,plain,(
% 0.19/0.46    r2_hidden(sK1,sK3(sK0,sK1)) | ~spl4_22),
% 0.19/0.46    inference(avatar_component_clause,[],[f203])).
% 0.19/0.46  fof(f203,plain,(
% 0.19/0.46    spl4_22 <=> r2_hidden(sK1,sK3(sK0,sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.19/0.46  fof(f295,plain,(
% 0.19/0.46    ( ! [X3] : (~r2_hidden(X3,sK3(sK0,sK1))) ) | (~spl4_4 | ~spl4_14)),
% 0.19/0.46    inference(resolution,[],[f290,f151])).
% 0.19/0.46  fof(f151,plain,(
% 0.19/0.46    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_14),
% 0.19/0.46    inference(avatar_component_clause,[],[f149])).
% 0.19/0.46  fof(f149,plain,(
% 0.19/0.46    spl4_14 <=> m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.19/0.46  fof(f290,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) ) | ~spl4_4),
% 0.19/0.46    inference(resolution,[],[f91,f67])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f89])).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    spl4_4 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.46  fof(f305,plain,(
% 0.19/0.46    ~spl4_27 | spl4_32),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f302])).
% 0.19/0.46  fof(f302,plain,(
% 0.19/0.46    $false | (~spl4_27 | spl4_32)),
% 0.19/0.46    inference(resolution,[],[f300,f279])).
% 0.19/0.46  fof(f279,plain,(
% 0.19/0.46    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_32),
% 0.19/0.46    inference(avatar_component_clause,[],[f278])).
% 0.19/0.46  fof(f278,plain,(
% 0.19/0.46    spl4_32 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.19/0.46  fof(f289,plain,(
% 0.19/0.46    spl4_33 | ~spl4_19 | ~spl4_26 | ~spl4_30 | ~spl4_32),
% 0.19/0.46    inference(avatar_split_clause,[],[f282,f278,f265,f224,f184,f286])).
% 0.19/0.46  fof(f224,plain,(
% 0.19/0.46    spl4_26 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.19/0.46  fof(f265,plain,(
% 0.19/0.46    spl4_30 <=> ! [X1,X0] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.19/0.46  fof(f282,plain,(
% 0.19/0.46    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl4_30 | ~spl4_32)),
% 0.19/0.46    inference(resolution,[],[f280,f268])).
% 0.19/0.46  fof(f268,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X0,sK0,k2_tarski(X1,X1))) ) | ~spl4_30),
% 0.19/0.46    inference(resolution,[],[f266,f70])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f66,f53])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f45])).
% 0.19/0.46  fof(f266,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_30),
% 0.19/0.46    inference(avatar_component_clause,[],[f265])).
% 0.19/0.46  fof(f280,plain,(
% 0.19/0.46    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl4_32),
% 0.19/0.46    inference(avatar_component_clause,[],[f278])).
% 0.19/0.46  fof(f281,plain,(
% 0.19/0.46    ~spl4_19 | spl4_32 | ~spl4_2 | ~spl4_31),
% 0.19/0.46    inference(avatar_split_clause,[],[f276,f271,f77,f278,f184])).
% 0.19/0.46  fof(f271,plain,(
% 0.19/0.46    spl4_31 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.19/0.46  fof(f276,plain,(
% 0.19/0.46    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_31)),
% 0.19/0.46    inference(resolution,[],[f274,f79])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    m1_connsp_2(sK2,sK0,sK1) | ~spl4_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f77])).
% 0.19/0.46  fof(f274,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_31),
% 0.19/0.46    inference(resolution,[],[f272,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.46    inference(cnf_transformation,[],[f40])).
% 0.19/0.46  % (3777)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,negated_conjecture,(
% 0.19/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.19/0.46    inference(negated_conjecture,[],[f13])).
% 0.19/0.46  fof(f13,conjecture,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.19/0.46  fof(f272,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_31),
% 0.19/0.46    inference(avatar_component_clause,[],[f271])).
% 0.19/0.46  fof(f273,plain,(
% 0.19/0.46    spl4_9 | ~spl4_10 | spl4_31),
% 0.19/0.46    inference(avatar_split_clause,[],[f269,f271,f126,f122])).
% 0.19/0.46  fof(f269,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(resolution,[],[f54,f48])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    l1_pre_topc(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f40])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f41])).
% 0.19/0.46  fof(f267,plain,(
% 0.19/0.46    ~spl4_10 | spl4_30),
% 0.19/0.46    inference(avatar_split_clause,[],[f263,f265,f126])).
% 0.19/0.46  fof(f263,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.46    inference(resolution,[],[f58,f48])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m2_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.46    inference(flattening,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.19/0.46  fof(f234,plain,(
% 0.19/0.46    ~spl4_3 | spl4_26),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f233])).
% 0.19/0.46  fof(f233,plain,(
% 0.19/0.46    $false | (~spl4_3 | spl4_26)),
% 0.19/0.46    inference(resolution,[],[f232,f87])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl4_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f85])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    spl4_3 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.46  fof(f232,plain,(
% 0.19/0.46    ~r2_hidden(sK1,u1_struct_0(sK0)) | spl4_26),
% 0.19/0.46    inference(resolution,[],[f226,f68])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f59,f53])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.19/0.46  fof(f226,plain,(
% 0.19/0.46    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_26),
% 0.19/0.46    inference(avatar_component_clause,[],[f224])).
% 0.19/0.46  fof(f231,plain,(
% 0.19/0.46    ~spl4_19 | ~spl4_26 | spl4_27 | ~spl4_1 | ~spl4_7 | ~spl4_25),
% 0.19/0.46    inference(avatar_split_clause,[],[f222,f219,f108,f73,f228,f224,f184])).
% 0.19/0.46  fof(f219,plain,(
% 0.19/0.46    spl4_25 <=> ! [X1,X0] : (~m2_connsp_2(X0,sK0,X1) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.19/0.46  fof(f222,plain,(
% 0.19/0.46    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_1 | ~spl4_7 | ~spl4_25)),
% 0.19/0.46    inference(resolution,[],[f220,f200])).
% 0.19/0.46  fof(f200,plain,(
% 0.19/0.46    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl4_1 | ~spl4_7)),
% 0.19/0.46    inference(forward_demodulation,[],[f75,f110])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl4_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f73])).
% 0.19/0.46  fof(f220,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_25),
% 0.19/0.46    inference(avatar_component_clause,[],[f219])).
% 0.19/0.46  fof(f221,plain,(
% 0.19/0.46    ~spl4_10 | spl4_25),
% 0.19/0.46    inference(avatar_split_clause,[],[f217,f219,f126])).
% 0.19/0.46  fof(f217,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~v2_pre_topc(sK0)) )),
% 0.19/0.46    inference(resolution,[],[f57,f48])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f42])).
% 0.19/0.46  fof(f206,plain,(
% 0.19/0.46    spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13 | spl4_22 | ~spl4_14 | ~spl4_17),
% 0.19/0.46    inference(avatar_split_clause,[],[f178,f173,f149,f203,f145,f141,f126,f122])).
% 0.19/0.46  fof(f173,plain,(
% 0.19/0.46    spl4_17 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.46  fof(f178,plain,(
% 0.19/0.46    ~m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_17),
% 0.19/0.46    inference(resolution,[],[f176,f63])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0,X1] : (m1_connsp_2(sK3(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ! [X0,X1] : (m1_connsp_2(sK3(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK3(X0,X1),X0,X1))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.19/0.47  fof(f176,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,X0)) ) | ~spl4_17),
% 0.19/0.47    inference(resolution,[],[f174,f49])).
% 0.19/0.47  fof(f174,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1)) ) | ~spl4_17),
% 0.19/0.47    inference(avatar_component_clause,[],[f173])).
% 0.19/0.47  fof(f189,plain,(
% 0.19/0.47    spl4_19),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f188])).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    $false | spl4_19),
% 0.19/0.47    inference(resolution,[],[f186,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_19),
% 0.19/0.47    inference(avatar_component_clause,[],[f184])).
% 0.19/0.47  fof(f175,plain,(
% 0.19/0.47    spl4_9 | ~spl4_10 | spl4_17),
% 0.19/0.47    inference(avatar_split_clause,[],[f171,f173,f126,f122])).
% 0.19/0.47  fof(f171,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f56,f48])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    spl4_13),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f155])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    $false | spl4_13),
% 0.19/0.47    inference(resolution,[],[f147,f49])).
% 0.19/0.47  fof(f147,plain,(
% 0.19/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl4_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f145])).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    spl4_12),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f153])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    $false | spl4_12),
% 0.19/0.47    inference(resolution,[],[f143,f48])).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | spl4_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f141])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13 | spl4_14 | ~spl4_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f139,f130,f149,f145,f141,f126,f122])).
% 0.19/0.47  fof(f130,plain,(
% 0.19/0.47    spl4_11 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.47  fof(f139,plain,(
% 0.19/0.47    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_11),
% 0.19/0.47    inference(resolution,[],[f137,f63])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_11),
% 0.19/0.47    inference(resolution,[],[f131,f49])).
% 0.19/0.47  fof(f131,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1)) ) | ~spl4_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f130])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    ~spl4_9),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f135])).
% 0.19/0.47  fof(f135,plain,(
% 0.19/0.47    $false | ~spl4_9),
% 0.19/0.47    inference(resolution,[],[f124,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ~v2_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    v2_struct_0(sK0) | ~spl4_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f122])).
% 0.19/0.47  fof(f134,plain,(
% 0.19/0.47    spl4_10),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f133])).
% 0.19/0.47  fof(f133,plain,(
% 0.19/0.47    $false | spl4_10),
% 0.19/0.47    inference(resolution,[],[f128,f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    v2_pre_topc(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | spl4_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f126])).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    spl4_9 | ~spl4_10 | spl4_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f120,f130,f126,f122])).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f62,f48])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    spl4_4 | spl4_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f104,f108,f89])).
% 0.19/0.47  fof(f104,plain,(
% 0.19/0.47    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f69,f49])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f61,f53])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.47    inference(flattening,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    spl4_3 | spl4_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f82,f89,f85])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.19/0.47    inference(resolution,[],[f60,f49])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.47    inference(flattening,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    ~spl4_1 | ~spl4_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f52,f77,f73])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl4_1 | spl4_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f51,f77,f73])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f40])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (3778)------------------------------
% 0.19/0.47  % (3778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (3778)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (3778)Memory used [KB]: 6268
% 0.19/0.47  % (3778)Time elapsed: 0.070 s
% 0.19/0.47  % (3778)------------------------------
% 0.19/0.47  % (3778)------------------------------
% 0.19/0.47  % (3776)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.47  % (3775)Success in time 0.12 s
%------------------------------------------------------------------------------

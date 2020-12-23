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
% DateTime   : Thu Dec  3 13:15:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 453 expanded)
%              Number of leaves         :   38 ( 180 expanded)
%              Depth                    :   11
%              Number of atoms          :  665 (2576 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11351)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f97,f132,f134,f136,f152,f154,f156,f167,f181,f190,f211,f213,f224,f230,f236,f245,f272,f276,f285,f289,f295,f299])).

fof(f299,plain,
    ( spl5_19
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl5_19
    | ~ spl5_27 ),
    inference(resolution,[],[f294,f290])).

fof(f290,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl5_19 ),
    inference(resolution,[],[f228,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f56])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f228,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_19
  <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f294,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl5_27
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f295,plain,
    ( ~ spl5_15
    | spl5_27
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f278,f243,f80,f292,f176])).

fof(f176,plain,
    ( spl5_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f80,plain,
    ( spl5_2
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f243,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f278,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(resolution,[],[f82,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(resolution,[],[f244,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_connsp_2(sK2,sK0,sK1)
      | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & ( m1_connsp_2(sK2,sK0,sK1)
      | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f243])).

fof(f82,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f289,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(resolution,[],[f284,f184])).

fof(f184,plain,
    ( ~ m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | spl5_1
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f77,f96])).

fof(f96,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_4
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f77,plain,
    ( ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_1
  <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f284,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl5_26
  <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f285,plain,
    ( spl5_26
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f240,f234,f227,f187,f176,f282])).

fof(f187,plain,
    ( spl5_16
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f234,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(resolution,[],[f239,f231])).

fof(f231,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl5_19 ),
    inference(resolution,[],[f229,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f56])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f229,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f227])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X0,sK0,k2_tarski(sK1,sK1)) )
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(resolution,[],[f238,f189])).

fof(f189,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m2_connsp_2(X0,sK0,k2_tarski(X1,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f235,f73])).

% (11347)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
        | m2_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f276,plain,
    ( ~ spl5_15
    | spl5_2
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f274,f270,f227,f80,f176])).

fof(f270,plain,
    ( spl5_25
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f274,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(resolution,[],[f273,f231])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_25 ),
    inference(resolution,[],[f271,f52])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_25 ),
    inference(avatar_split_clause,[],[f268,f270,f126,f122])).

fof(f122,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f126,plain,
    ( spl5_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(X1,sK0,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f245,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_21 ),
    inference(avatar_split_clause,[],[f241,f243,f126,f122])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f51])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f236,plain,
    ( ~ spl5_8
    | spl5_20 ),
    inference(avatar_split_clause,[],[f232,f234,f126])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m2_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f230,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | spl5_19
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f225,f222,f94,f76,f227,f187,f176])).

fof(f222,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | r1_tarski(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f225,plain,
    ( r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(resolution,[],[f223,f191])).

fof(f191,plain,
    ( m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f78,f96])).

fof(f78,plain,
    ( m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m2_connsp_2(X0,sK0,X1)
        | r1_tarski(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( ~ spl5_8
    | spl5_18 ),
    inference(avatar_split_clause,[],[f220,f222,f126])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ m2_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k1_tops_1(sK0,X0))
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f61,f51])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f213,plain,
    ( ~ spl5_3
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(resolution,[],[f210,f160])).

fof(f160,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(resolution,[],[f157,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f157,plain,
    ( v1_xboole_0(sK4(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(resolution,[],[f151,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f92,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f151,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_12
  <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f210,plain,
    ( r2_hidden(sK1,sK4(sK0,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_17
  <=> r2_hidden(sK1,sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f211,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | spl5_17
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f170,f165,f149,f208,f145,f141,f126,f122])).

fof(f141,plain,
    ( spl5_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f145,plain,
    ( spl5_11
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f165,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f170,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK4(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_13 ),
    inference(resolution,[],[f168,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK4(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK4(X0,X1),X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f168,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f166,f52])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f190,plain,
    ( spl5_3
    | ~ spl5_11
    | spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f185,f94,f187,f145,f90])).

fof(f185,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(superposition,[],[f66,f96])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f181,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f178,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f167,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_13 ),
    inference(avatar_split_clause,[],[f163,f165,f126,f122])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f156,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f147,f52])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f154,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f143,f51])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f152,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f139,f130,f149,f145,f141,f126,f122])).

fof(f130,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f139,plain,
    ( m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f137,f68])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_9 ),
    inference(resolution,[],[f131,f52])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f136,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f134,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f128,f50])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f132,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f120,f130,f126,f122])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f97,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f86,f94,f90])).

fof(f86,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f84,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f55,f80,f76])).

fof(f55,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f54,f80,f76])).

fof(f54,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11343)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (11358)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (11349)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (11345)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (11357)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (11346)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (11354)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (11345)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (11356)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (11352)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (11360)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (11353)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (11351)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f83,f84,f97,f132,f134,f136,f152,f154,f156,f167,f181,f190,f211,f213,f224,f230,f236,f245,f272,f276,f285,f289,f295,f299])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    spl5_19 | ~spl5_27),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f296])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    $false | (spl5_19 | ~spl5_27)),
% 0.21/0.51    inference(resolution,[],[f294,f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl5_19),
% 0.21/0.51    inference(resolution,[],[f228,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f71,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ~r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | spl5_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl5_19 <=> r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f292])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl5_27 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ~spl5_15 | spl5_27 | ~spl5_2 | ~spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f278,f243,f80,f292,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl5_15 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl5_2 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    spl5_21 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_21)),
% 0.21/0.51    inference(resolution,[],[f82,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.51    inference(resolution,[],[f244,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    (((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : ((~m1_connsp_2(X2,sK0,X1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & (m1_connsp_2(X2,sK0,X1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X2] : ((~m1_connsp_2(X2,sK0,sK1) | ~m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(X2,sK0,sK1) | m2_connsp_2(X2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & (m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (((~m1_connsp_2(X2,X0,X1) | ~m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))) & (m1_connsp_2(X2,X0,X1) | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <~> m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) <=> m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f243])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    m1_connsp_2(sK2,sK0,sK1) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    spl5_1 | ~spl5_4 | ~spl5_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    $false | (spl5_1 | ~spl5_4 | ~spl5_26)),
% 0.21/0.51    inference(resolution,[],[f284,f184])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (spl5_1 | ~spl5_4)),
% 0.21/0.51    inference(backward_demodulation,[],[f77,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl5_4 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl5_1 <=> m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | ~spl5_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f282])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    spl5_26 <=> m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    spl5_26 | ~spl5_15 | ~spl5_16 | ~spl5_19 | ~spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f240,f234,f227,f187,f176,f282])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl5_16 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    spl5_20 <=> ! [X1,X0] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl5_16 | ~spl5_19 | ~spl5_20)),
% 0.21/0.51    inference(resolution,[],[f239,f231])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~spl5_19),
% 0.21/0.51    inference(resolution,[],[f229,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f70,f56])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~spl5_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f227])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X0,sK0,k2_tarski(sK1,sK1))) ) | (~spl5_16 | ~spl5_20)),
% 0.21/0.51    inference(resolution,[],[f238,f189])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f187])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X0,sK0,k2_tarski(X1,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_tops_1(sK0,X0))) ) | ~spl5_20),
% 0.21/0.51    inference(resolution,[],[f235,f73])).
% 0.21/0.51  % (11347)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | m2_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f234])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ~spl5_15 | spl5_2 | ~spl5_19 | ~spl5_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f274,f270,f227,f80,f176])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl5_25 <=> ! [X1,X0] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_19 | ~spl5_25)),
% 0.21/0.51    inference(resolution,[],[f273,f231])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_25),
% 0.21/0.51    inference(resolution,[],[f271,f52])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | spl5_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f268,f270,f126,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl5_7 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl5_8 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f59,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f241,f243,f126,f122])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f58,f51])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~spl5_8 | spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f232,f234,f126])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m2_connsp_2(X1,sK0,X0) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f62,f51])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m2_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ~spl5_15 | ~spl5_16 | spl5_19 | ~spl5_1 | ~spl5_4 | ~spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f225,f222,f94,f76,f227,f187,f176])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    spl5_18 <=> ! [X1,X0] : (~m2_connsp_2(X0,sK0,X1) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    r1_tarski(k2_tarski(sK1,sK1),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_4 | ~spl5_18)),
% 0.21/0.51    inference(resolution,[],[f223,f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    m2_connsp_2(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl5_1 | ~spl5_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f78,f96])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f222])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~spl5_8 | spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f220,f222,f126])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m2_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,k1_tops_1(sK0,X0)) | ~v2_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f61,f51])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~spl5_3 | ~spl5_12 | ~spl5_17),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    $false | (~spl5_3 | ~spl5_12 | ~spl5_17)),
% 0.21/0.51    inference(resolution,[],[f210,f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK4(sK0,sK1))) ) | (~spl5_3 | ~spl5_12)),
% 0.21/0.51    inference(resolution,[],[f157,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(rectify,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    v1_xboole_0(sK4(sK0,sK1)) | (~spl5_3 | ~spl5_12)),
% 0.21/0.51    inference(resolution,[],[f151,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f92,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl5_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl5_12 <=> m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    r2_hidden(sK1,sK4(sK0,sK1)) | ~spl5_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl5_17 <=> r2_hidden(sK1,sK4(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | spl5_17 | ~spl5_12 | ~spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f170,f165,f149,f208,f145,f141,f126,f122])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl5_10 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl5_11 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl5_13 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK4(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_13),
% 0.21/0.51    inference(resolution,[],[f168,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_connsp_2(sK4(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_connsp_2(sK4(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK4(X0,X1),X0,X1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,X0)) ) | ~spl5_13),
% 0.21/0.51    inference(resolution,[],[f166,f52])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1)) ) | ~spl5_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    spl5_3 | ~spl5_11 | spl5_16 | ~spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f94,f187,f145,f90])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_4),
% 0.21/0.51    inference(superposition,[],[f66,f96])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl5_15),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    $false | spl5_15),
% 0.21/0.51    inference(resolution,[],[f178,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f163,f165,f126,f122])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f60,f51])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl5_11),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    $false | spl5_11),
% 0.21/0.51    inference(resolution,[],[f147,f52])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl5_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    $false | spl5_10),
% 0.21/0.51    inference(resolution,[],[f143,f51])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | spl5_12 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f130,f149,f145,f141,f126,f122])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl5_9 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    m1_subset_1(sK4(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 0.21/0.51    inference(resolution,[],[f137,f68])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_9),
% 0.21/0.51    inference(resolution,[],[f131,f52])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,X1)) ) | ~spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f130])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~spl5_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    $false | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f124,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl5_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    $false | spl5_8),
% 0.21/0.51    inference(resolution,[],[f128,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl5_7 | ~spl5_8 | spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f130,f126,f122])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f67,f51])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl5_3 | spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f86,f94,f90])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f72,f52])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f65,f56])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f80,f76])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~m1_connsp_2(sK2,sK0,sK1) | ~m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_1 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f80,f76])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_connsp_2(sK2,sK0,sK1) | m2_connsp_2(sK2,sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (11345)------------------------------
% 0.21/0.51  % (11345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11345)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (11345)Memory used [KB]: 6268
% 0.21/0.51  % (11345)Time elapsed: 0.076 s
% 0.21/0.51  % (11354)Refutation not found, incomplete strategy% (11354)------------------------------
% 0.21/0.51  % (11354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11354)Memory used [KB]: 10746
% 0.21/0.51  % (11354)Time elapsed: 0.083 s
% 0.21/0.51  % (11354)------------------------------
% 0.21/0.51  % (11354)------------------------------
% 0.21/0.51  % (11345)------------------------------
% 0.21/0.51  % (11345)------------------------------
% 0.21/0.52  % (11342)Success in time 0.151 s
%------------------------------------------------------------------------------

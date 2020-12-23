%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1091+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 162 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 550 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f57,f67,f76,f84,f108,f113,f124,f128,f136])).

fof(f136,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f131,f115])).

fof(f115,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f49,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_finset_1(X0)
      | r2_hidden(sK2(X0),X0)
      | v1_finset_1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f49,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_2
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f131,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | spl3_9
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f123,f127])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | v1_finset_1(X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_10
  <=> ! [X2] :
        ( v1_finset_1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f123,plain,
    ( ~ v1_finset_1(sK2(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_9
  <=> v1_finset_1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f128,plain,
    ( spl3_10
    | spl3_2 ),
    inference(avatar_split_clause,[],[f26,f48,f126])).

fof(f26,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ v1_finset_1(X1)
        & r2_hidden(X1,sK0) )
   => ( ~ v1_finset_1(sK1)
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f124,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f116,f48,f44,f121])).

fof(f116,plain,
    ( ~ v1_finset_1(sK2(sK0))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f49,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK2(X0))
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,
    ( ~ spl3_2
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_2
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f111,f77])).

fof(f77,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k3_tarski(sK0)))
    | ~ spl3_2
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f50,f75,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | v1_finset_1(X1) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

fof(f75,plain,
    ( ~ v1_finset_1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_4
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f111,plain,
    ( m1_subset_1(sK1,k9_setfam_1(k3_tarski(sK0)))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f107,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f107,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_8
  <=> r1_tarski(sK1,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f85,f81,f105])).

fof(f81,plain,
    ( spl3_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( r1_tarski(sK1,k3_tarski(sK0))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f83,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f83,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( ~ spl3_1
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f48,f81,f44])).

fof(f68,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f27,f50])).

fof(f27,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f69,f48,f73,f44])).

fof(f69,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f28,f50])).

fof(f28,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(X0,k9_setfam_1(k9_setfam_1(k3_tarski(X0)))) ),
    inference(unit_resulting_resolution,[],[f38,f41])).

fof(f38,plain,(
    ! [X0] : r1_tarski(X0,k9_setfam_1(k3_tarski(X0))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f63,plain,
    ( ~ m1_subset_1(sK0,k9_setfam_1(k9_setfam_1(k3_tarski(sK0))))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f45,f56,f40])).

fof(f56,plain,
    ( v1_finset_1(k9_setfam_1(k3_tarski(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_3
  <=> v1_finset_1(k9_setfam_1(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( ~ v1_finset_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f57,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f48,f54])).

fof(f52,plain,
    ( v1_finset_1(k9_setfam_1(k3_tarski(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_finset_1(k9_setfam_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f51,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f48,f44])).

fof(f25,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------

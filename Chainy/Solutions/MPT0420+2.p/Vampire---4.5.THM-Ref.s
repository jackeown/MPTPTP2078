%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0420+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 119 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  185 ( 417 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1168,f1173,f1182,f1183,f1898,f1903,f1908,f1976,f2096,f2228])).

fof(f2228,plain,
    ( ~ spl29_1
    | ~ spl29_3
    | spl29_4
    | ~ spl29_17
    | ~ spl29_19 ),
    inference(avatar_contradiction_clause,[],[f2227])).

fof(f2227,plain,
    ( $false
    | ~ spl29_1
    | ~ spl29_3
    | spl29_4
    | ~ spl29_17
    | ~ spl29_19 ),
    inference(subsumption_resolution,[],[f2226,f1177])).

fof(f1177,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl29_3 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl29_3
  <=> r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f2226,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl29_1
    | spl29_4
    | ~ spl29_17
    | ~ spl29_19 ),
    inference(forward_demodulation,[],[f2215,f1975])).

fof(f1975,plain,
    ( sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2))
    | ~ spl29_19 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f1973,plain,
    ( spl29_19
  <=> sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_19])])).

fof(f2215,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)))
    | ~ spl29_1
    | spl29_4
    | ~ spl29_17 ),
    inference(unit_resulting_resolution,[],[f1167,f1180,f1902,f896])).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f633])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f632])).

fof(f632,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f605])).

fof(f605,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f1902,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_17 ),
    inference(avatar_component_clause,[],[f1900])).

fof(f1900,plain,
    ( spl29_17
  <=> m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_17])])).

fof(f1180,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | spl29_4 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f1179,plain,
    ( spl29_4
  <=> r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f1167,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_1 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f1165,plain,
    ( spl29_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).

fof(f2096,plain,
    ( ~ spl29_2
    | spl29_3
    | ~ spl29_4
    | ~ spl29_16
    | ~ spl29_18 ),
    inference(avatar_contradiction_clause,[],[f2095])).

fof(f2095,plain,
    ( $false
    | ~ spl29_2
    | spl29_3
    | ~ spl29_4
    | ~ spl29_16
    | ~ spl29_18 ),
    inference(subsumption_resolution,[],[f2094,f1181])).

fof(f1181,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f1179])).

fof(f2094,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl29_2
    | spl29_3
    | ~ spl29_16
    | ~ spl29_18 ),
    inference(forward_demodulation,[],[f2074,f1907])).

fof(f1907,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl29_18 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1905,plain,
    ( spl29_18
  <=> sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_18])])).

fof(f2074,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK2))
    | ~ spl29_2
    | spl29_3
    | ~ spl29_16 ),
    inference(unit_resulting_resolution,[],[f1176,f1172,f1897,f896])).

fof(f1897,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_16 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f1895,plain,
    ( spl29_16
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_16])])).

fof(f1172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_2 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1170,plain,
    ( spl29_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).

fof(f1176,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | spl29_3 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1976,plain,
    ( spl29_19
    | ~ spl29_2 ),
    inference(avatar_split_clause,[],[f1426,f1170,f1973])).

fof(f1426,plain,
    ( sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2))
    | ~ spl29_2 ),
    inference(unit_resulting_resolution,[],[f1172,f901])).

fof(f901,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f638])).

fof(f638,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f564])).

fof(f564,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f1908,plain,
    ( spl29_18
    | ~ spl29_1 ),
    inference(avatar_split_clause,[],[f1425,f1165,f1905])).

fof(f1425,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl29_1 ),
    inference(unit_resulting_resolution,[],[f1167,f901])).

fof(f1903,plain,
    ( spl29_17
    | ~ spl29_2 ),
    inference(avatar_split_clause,[],[f1417,f1170,f1900])).

fof(f1417,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_2 ),
    inference(unit_resulting_resolution,[],[f1172,f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f637])).

fof(f637,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f1898,plain,
    ( spl29_16
    | ~ spl29_1 ),
    inference(avatar_split_clause,[],[f1416,f1165,f1895])).

fof(f1416,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl29_1 ),
    inference(unit_resulting_resolution,[],[f1167,f900])).

fof(f1183,plain,
    ( ~ spl29_3
    | ~ spl29_4 ),
    inference(avatar_split_clause,[],[f873,f1179,f1175])).

fof(f873,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f770])).

fof(f770,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f767,f769,f768])).

fof(f768,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | r1_tarski(k7_setfam_1(X0,X1),X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f769,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
          | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
        & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
          | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
        | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
      & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
        | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f767,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f766])).

fof(f766,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f617])).

fof(f617,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <~> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f607])).

fof(f607,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),X2)
            <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f606])).

fof(f606,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f1182,plain,
    ( spl29_3
    | spl29_4 ),
    inference(avatar_split_clause,[],[f872,f1179,f1175])).

fof(f872,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f770])).

fof(f1173,plain,(
    spl29_2 ),
    inference(avatar_split_clause,[],[f871,f1170])).

fof(f871,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f770])).

fof(f1168,plain,(
    spl29_1 ),
    inference(avatar_split_clause,[],[f870,f1165])).

fof(f870,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f770])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:28 EST 2020

% Result     : Theorem 6.33s
% Output     : Refutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :  333 (1216 expanded)
%              Number of leaves         :   62 ( 383 expanded)
%              Depth                    :   29
%              Number of atoms          : 1139 (4368 expanded)
%              Number of equality atoms :  199 ( 814 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9987,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f116,f118,f122,f130,f138,f143,f154,f207,f218,f261,f267,f401,f445,f494,f619,f658,f692,f937,f1268,f1276,f1296,f1426,f1500,f4565,f4572,f4883,f5220,f6563,f6981,f8591,f9227,f9448,f9517,f9607,f9754,f9834,f9941,f9964,f9966,f9978,f9980,f9986])).

fof(f9986,plain,
    ( ~ spl7_15
    | ~ spl7_22
    | ~ spl7_23
    | spl7_60 ),
    inference(avatar_contradiction_clause,[],[f9985])).

fof(f9985,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_22
    | ~ spl7_23
    | spl7_60 ),
    inference(resolution,[],[f691,f9849])).

fof(f9849,plain,
    ( ! [X9] : r1_tarski(k2_relat_1(sK2),X9)
    | ~ spl7_15
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f364,f9732])).

fof(f9732,plain,
    ( ! [X8] : r1_tarski(sK0,X8)
    | ~ spl7_15
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f276,f206])).

fof(f206,plain,
    ( ! [X1] : r1_tarski(k2_relat_1(sK2),X1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_15
  <=> ! [X1] : r1_tarski(k2_relat_1(sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f276,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK6(sK0,X8)))
        | r1_tarski(sK0,X8) )
    | ~ spl7_22 ),
    inference(resolution,[],[f268,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f268,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK6(sK0,X0)),k2_relat_1(sK2))
        | r1_tarski(sK0,X0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f260,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f364,plain,
    ( ! [X9] :
        ( ~ r1_tarski(sK0,sK5(sK2,k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X9)))))
        | r1_tarski(k2_relat_1(sK2),X9) )
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(resolution,[],[f334,f80])).

fof(f334,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X0)))),sK0)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(resolution,[],[f285,f266])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(sK5(sK2,X0),sK0) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl7_23
  <=> ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f285,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X0))),k2_relat_1(sK2))
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(resolution,[],[f270,f260])).

fof(f270,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,sK6(k2_relat_1(sK2),X0)),sK0)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_23 ),
    inference(resolution,[],[f266,f73])).

fof(f691,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0))
    | spl7_60 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl7_60
  <=> r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f9980,plain,
    ( ~ spl7_15
    | ~ spl7_22
    | spl7_278 ),
    inference(avatar_contradiction_clause,[],[f9979])).

fof(f9979,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_22
    | spl7_278 ),
    inference(resolution,[],[f9977,f9732])).

fof(f9977,plain,
    ( ~ r1_tarski(sK0,sK3(sK2,sK0))
    | spl7_278 ),
    inference(avatar_component_clause,[],[f9976])).

fof(f9976,plain,
    ( spl7_278
  <=> r1_tarski(sK0,sK3(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f9978,plain,
    ( ~ spl7_278
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f9974,f675,f9976])).

fof(f675,plain,
    ( spl7_56
  <=> r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f9974,plain,
    ( ~ r1_tarski(sK0,sK3(sK2,sK0))
    | ~ spl7_56 ),
    inference(resolution,[],[f676,f80])).

fof(f676,plain,
    ( r2_hidden(sK3(sK2,sK0),sK0)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f675])).

fof(f9966,plain,
    ( ~ spl7_15
    | ~ spl7_22
    | ~ spl7_23
    | spl7_276 ),
    inference(avatar_contradiction_clause,[],[f9965])).

fof(f9965,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_22
    | ~ spl7_23
    | spl7_276 ),
    inference(resolution,[],[f9963,f9849])).

fof(f9963,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0)))
    | spl7_276 ),
    inference(avatar_component_clause,[],[f9962])).

fof(f9962,plain,
    ( spl7_276
  <=> r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f9964,plain,
    ( ~ spl7_276
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f9956,f650,f9962])).

fof(f650,plain,
    ( spl7_52
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f9956,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0)))
    | ~ spl7_52 ),
    inference(resolution,[],[f651,f80])).

fof(f651,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f650])).

fof(f9941,plain,
    ( ~ spl7_17
    | spl7_91 ),
    inference(avatar_contradiction_clause,[],[f9940])).

fof(f9940,plain,
    ( $false
    | ~ spl7_17
    | spl7_91 ),
    inference(resolution,[],[f1005,f217])).

fof(f217,plain,
    ( ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_17
  <=> ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f1005,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0)))
    | spl7_91 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1004,plain,
    ( spl7_91
  <=> r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f9834,plain,
    ( spl7_3
    | ~ spl7_10
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f9833])).

fof(f9833,plain,
    ( $false
    | spl7_3
    | ~ spl7_10
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f158,f1427])).

fof(f1427,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl7_3
    | ~ spl7_35 ),
    inference(resolution,[],[f111,f453])).

fof(f453,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
    | ~ spl7_35 ),
    inference(resolution,[],[f444,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f444,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl7_35
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f111,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f158,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f9754,plain,
    ( ~ spl7_15
    | ~ spl7_22
    | spl7_81 ),
    inference(avatar_contradiction_clause,[],[f9734])).

fof(f9734,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_22
    | spl7_81 ),
    inference(subsumption_resolution,[],[f936,f9732])).

fof(f936,plain,
    ( ~ r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0))))
    | spl7_81 ),
    inference(avatar_component_clause,[],[f935])).

fof(f935,plain,
    ( spl7_81
  <=> r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f9607,plain,
    ( spl7_49
    | spl7_48
    | ~ spl7_17
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f1365,f617,f216,f635,f638])).

fof(f638,plain,
    ( spl7_49
  <=> k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f635,plain,
    ( spl7_48
  <=> sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f617,plain,
    ( spl7_46
  <=> ! [X0] :
        ( sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK3(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1365,plain,
    ( sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0)))
    | k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | ~ spl7_17
    | ~ spl7_46 ),
    inference(resolution,[],[f622,f217])).

fof(f622,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK3(sK2,X5))
        | sK3(sK2,X5) = k1_funct_1(sK2,sK4(sK2,X5))
        | k2_relat_1(sK2) = X5 )
    | ~ spl7_46 ),
    inference(resolution,[],[f618,f80])).

fof(f618,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0)) )
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f617])).

fof(f9517,plain,
    ( spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f9365,f152,f157])).

fof(f152,plain,
    ( spl7_9
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f9365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl7_9 ),
    inference(resolution,[],[f76,f153])).

fof(f153,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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

fof(f9448,plain,
    ( ~ spl7_91
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f991,f910,f1004])).

fof(f910,plain,
    ( spl7_76
  <=> r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f991,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0)))
    | ~ spl7_76 ),
    inference(resolution,[],[f911,f80])).

fof(f911,plain,
    ( r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f910])).

fof(f9227,plain,
    ( ~ spl7_99
    | spl7_200 ),
    inference(avatar_contradiction_clause,[],[f9226])).

fof(f9226,plain,
    ( $false
    | ~ spl7_99
    | spl7_200 ),
    inference(subsumption_resolution,[],[f6980,f1272])).

fof(f1272,plain,
    ( ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ spl7_99 ),
    inference(avatar_component_clause,[],[f1271])).

fof(f1271,plain,
    ( spl7_99
  <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f6980,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl7_200 ),
    inference(avatar_component_clause,[],[f6979])).

fof(f6979,plain,
    ( spl7_200
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f8591,plain,
    ( sK0 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
    | sK0 = k2_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6981,plain,
    ( ~ spl7_200
    | ~ spl7_100
    | spl7_105 ),
    inference(avatar_split_clause,[],[f5359,f1498,f1274,f6979])).

fof(f1274,plain,
    ( spl7_100
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f1498,plain,
    ( spl7_105
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f5359,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_100
    | spl7_105 ),
    inference(superposition,[],[f1499,f1551])).

fof(f1551,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1499,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl7_105 ),
    inference(avatar_component_clause,[],[f1498])).

fof(f6563,plain,
    ( spl7_98
    | spl7_14
    | ~ spl7_35
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f6562,f1424,f443,f201,f1259])).

fof(f1259,plain,
    ( spl7_98
  <=> ! [X1,X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f201,plain,
    ( spl7_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1424,plain,
    ( spl7_104
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f6562,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_35
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f1464,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1464,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_35
    | ~ spl7_104 ),
    inference(superposition,[],[f453,f1425])).

fof(f1425,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f5220,plain,
    ( spl7_100
    | ~ spl7_6
    | spl7_126 ),
    inference(avatar_split_clause,[],[f5219,f4881,f125,f1274])).

fof(f125,plain,
    ( spl7_6
  <=> ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f4881,plain,
    ( spl7_126
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f5219,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6
    | spl7_126 ),
    inference(resolution,[],[f4882,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f4882,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl7_126 ),
    inference(avatar_component_clause,[],[f4881])).

fof(f4883,plain,
    ( ~ spl7_126
    | spl7_2
    | ~ spl7_101
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f4879,f1424,f1282,f107,f4881])).

fof(f107,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1282,plain,
    ( spl7_101
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f4879,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl7_2
    | ~ spl7_101
    | ~ spl7_104 ),
    inference(forward_demodulation,[],[f4633,f1425])).

fof(f4633,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl7_2
    | ~ spl7_101 ),
    inference(superposition,[],[f108,f1283])).

fof(f1283,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f108,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f4572,plain,
    ( spl7_100
    | ~ spl7_120 ),
    inference(avatar_contradiction_clause,[],[f4570])).

fof(f4570,plain,
    ( $false
    | spl7_100
    | ~ spl7_120 ),
    inference(subsumption_resolution,[],[f1275,f4564])).

fof(f4564,plain,
    ( ! [X325] : k1_xboole_0 = X325
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f4563])).

fof(f4563,plain,
    ( spl7_120
  <=> ! [X325] : k1_xboole_0 = X325 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f1275,plain,
    ( k1_xboole_0 != sK0
    | spl7_100 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f4565,plain,
    ( spl7_101
    | spl7_120
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(avatar_split_clause,[],[f4418,f1294,f916,f216,f4563,f1282])).

fof(f916,plain,
    ( spl7_78
  <=> sK0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f1294,plain,
    ( spl7_103
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f4418,plain,
    ( ! [X325] :
        ( k1_xboole_0 = X325
        | k1_xboole_0 = sK2 )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(trivial_inequality_removal,[],[f4372])).

fof(f4372,plain,
    ( ! [X325] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X325
        | k1_xboole_0 = sK2 )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(superposition,[],[f77,f4242])).

fof(f4242,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,sK2)
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f4092,f3019])).

fof(f3019,plain,
    ( ! [X5] : m1_subset_1(k2_zfmisc_1(X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,sK0)))
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2942,f76])).

fof(f2942,plain,
    ( ! [X99] : r1_tarski(k2_zfmisc_1(X99,sK2),k2_zfmisc_1(X99,sK0))
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(superposition,[],[f1746,f2834])).

fof(f2834,plain,
    ( ! [X12] : sK0 = k2_relat_1(k2_zfmisc_1(X12,sK2))
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2824,f1018])).

fof(f1018,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | sK0 = X1 )
    | ~ spl7_17
    | ~ spl7_78 ),
    inference(superposition,[],[f219,f917])).

fof(f917,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f916])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(k1_xboole_0))
        | k2_relat_1(k1_xboole_0) = X0 )
    | ~ spl7_17 ),
    inference(resolution,[],[f217,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2824,plain,
    ( ! [X10] : r1_tarski(k2_relat_1(k2_zfmisc_1(X10,sK2)),sK0)
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2809,f141])).

fof(f141,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f76,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2809,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(k2_zfmisc_1(X4,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | r1_tarski(k2_relat_1(k2_zfmisc_1(X4,sK2)),sK0) )
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2401,f191])).

fof(f191,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | r1_tarski(k2_relat_1(k2_zfmisc_1(X2,X3)),X4) ) ),
    inference(resolution,[],[f175,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f82,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2401,plain,
    ( ! [X14,X15,X13,X16] :
        ( m1_subset_1(k2_zfmisc_1(X13,sK2),k1_zfmisc_1(k2_zfmisc_1(X16,sK0)))
        | ~ m1_subset_1(k2_zfmisc_1(X13,sK2),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2209,f76])).

fof(f2209,plain,
    ( ! [X6,X4,X5,X3] :
        ( r1_tarski(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X6,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(X3,sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2206,f1851])).

fof(f1851,plain,
    ( ! [X17,X18] :
        ( ~ r1_tarski(X17,k1_xboole_0)
        | r1_tarski(X17,k2_zfmisc_1(X18,sK0)) )
    | ~ spl7_78 ),
    inference(resolution,[],[f1823,f1811])).

fof(f1811,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))
    | ~ spl7_78 ),
    inference(forward_demodulation,[],[f1807,f917])).

fof(f1807,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0))) ),
    inference(superposition,[],[f1746,f96])).

fof(f1823,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f1817])).

fof(f1817,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f185,f73])).

fof(f185,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK6(X4,X3),X5)
      | r1_tarski(X4,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X5,X2) ) ),
    inference(resolution,[],[f174,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f174,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK6(X3,X4),X5)
      | ~ r1_tarski(X5,X4)
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f72,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2206,plain,
    ( ! [X8,X7,X9] :
        ( r1_tarski(k2_zfmisc_1(X7,sK2),k1_xboole_0)
        | ~ m1_subset_1(k2_zfmisc_1(X7,sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
    | ~ spl7_103 ),
    inference(resolution,[],[f1976,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1976,plain,
    ( ! [X2,X3,X1] :
        ( m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl7_103 ),
    inference(forward_demodulation,[],[f1968,f96])).

fof(f1968,plain,
    ( ! [X2,X3,X1] :
        ( m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0)))
        | ~ m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl7_103 ),
    inference(resolution,[],[f1942,f89])).

fof(f1942,plain,
    ( ! [X47] : r1_tarski(k2_relat_1(k2_zfmisc_1(X47,sK2)),k1_xboole_0)
    | ~ spl7_103 ),
    inference(resolution,[],[f1903,f1860])).

fof(f1860,plain,
    ( ! [X34] :
        ( ~ r1_tarski(X34,sK2)
        | r1_tarski(X34,k1_xboole_0) )
    | ~ spl7_103 ),
    inference(resolution,[],[f1823,f1295])).

fof(f1295,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1903,plain,(
    ! [X12,X13] : r1_tarski(k2_relat_1(k2_zfmisc_1(X12,X13)),X13) ),
    inference(resolution,[],[f191,f141])).

fof(f1746,plain,(
    ! [X4,X5] : r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_relat_1(k2_zfmisc_1(X4,X5)))) ),
    inference(resolution,[],[f1238,f141])).

fof(f1238,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(X0,k2_zfmisc_1(X1,k2_relat_1(X0))) ) ),
    inference(resolution,[],[f433,f75])).

fof(f433,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k2_relat_1(X3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f89,f94])).

fof(f4092,plain,
    ( ! [X12,X13,X11] :
        ( ~ m1_subset_1(k2_zfmisc_1(X11,sK2),k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | k1_xboole_0 = k2_zfmisc_1(X11,sK2) )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(subsumption_resolution,[],[f2211,f4087])).

fof(f4087,plain,
    ( ! [X2,X1] : r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X2))
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f4083,f1815])).

fof(f1815,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ spl7_78 ),
    inference(resolution,[],[f1811,f76])).

fof(f4083,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(superposition,[],[f4069,f97])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4069,plain,
    ( ! [X21,X19,X20,X18] :
        ( r1_tarski(k2_zfmisc_1(X18,sK2),k2_zfmisc_1(X19,X21))
        | ~ m1_subset_1(k2_zfmisc_1(X18,sK2),k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2844,f75])).

fof(f2844,plain,
    ( ! [X4,X2,X5,X3] :
        ( m1_subset_1(k2_zfmisc_1(X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m1_subset_1(k2_zfmisc_1(X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X5))) )
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2833,f89])).

fof(f2833,plain,
    ( ! [X10,X11] : r1_tarski(k2_relat_1(k2_zfmisc_1(X10,sK2)),X11)
    | ~ spl7_17
    | ~ spl7_78
    | ~ spl7_103 ),
    inference(resolution,[],[f2824,f1020])).

fof(f1020,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,sK0)
        | r1_tarski(X3,X4) )
    | ~ spl7_17
    | ~ spl7_78 ),
    inference(superposition,[],[f222,f917])).

fof(f222,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,k2_relat_1(k1_xboole_0))
        | r1_tarski(X3,X4) )
    | ~ spl7_17 ),
    inference(resolution,[],[f217,f177])).

fof(f177,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,sK6(X2,X4))
      | ~ r1_tarski(X2,X3)
      | r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f173,f73])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f72,f80])).

fof(f2211,plain,
    ( ! [X12,X13,X11] :
        ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X11,sK2))
        | k1_xboole_0 = k2_zfmisc_1(X11,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(X11,sK2),k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
    | ~ spl7_103 ),
    inference(resolution,[],[f2206,f71])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1500,plain,
    ( ~ spl7_105
    | spl7_2
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f1440,f1424,f107,f1498])).

fof(f1440,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl7_2
    | ~ spl7_104 ),
    inference(superposition,[],[f108,f1425])).

fof(f1426,plain,
    ( ~ spl7_3
    | spl7_104
    | spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1419,f114,f107,f1424,f110])).

fof(f114,plain,
    ( spl7_4
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1419,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f1418,f108])).

fof(f1418,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f1416])).

fof(f1416,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_4 ),
    inference(superposition,[],[f572,f115])).

fof(f115,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f572,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f85,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1296,plain,
    ( spl7_103
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1292,f201,f1294])).

fof(f1292,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_14 ),
    inference(resolution,[],[f1261,f75])).

fof(f1261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1276,plain,
    ( spl7_99
    | ~ spl7_14
    | ~ spl7_100
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1186,f114,f1274,f201,f1271])).

fof(f1186,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl7_4 ),
    inference(superposition,[],[f333,f115])).

fof(f333,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f331,f97])).

fof(f331,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f132,f81])).

fof(f132,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f101,f97])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1268,plain,
    ( ~ spl7_10
    | ~ spl7_98 ),
    inference(avatar_contradiction_clause,[],[f1264])).

fof(f1264,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f158,f1260])).

fof(f1260,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f937,plain,
    ( spl7_76
    | ~ spl7_81
    | spl7_78
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_39
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f933,f656,f635,f492,f265,f259,f916,f935,f910])).

fof(f492,plain,
    ( spl7_39
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK3(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f656,plain,
    ( spl7_54
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f933,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0))))
    | r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_39
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(forward_demodulation,[],[f900,f657])).

fof(f657,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f656])).

fof(f900,plain,
    ( ~ r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0))))
    | r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_39
    | ~ spl7_48 ),
    inference(superposition,[],[f550,f636])).

fof(f636,plain,
    ( sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f635])).

fof(f550,plain,
    ( ! [X9] :
        ( ~ r1_tarski(sK0,sK5(sK2,k1_funct_1(sK2,sK4(sK2,X9))))
        | r2_hidden(sK3(sK2,X9),X9)
        | k2_relat_1(sK2) = X9 )
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_39 ),
    inference(resolution,[],[f510,f80])).

fof(f510,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK2,k1_funct_1(sK2,sK4(sK2,X1))),sK0)
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK3(sK2,X1),X1) )
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_39 ),
    inference(resolution,[],[f495,f266])).

fof(f495,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK4(sK2,X0)),k2_relat_1(sK2))
        | r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl7_22
    | ~ spl7_39 ),
    inference(resolution,[],[f493,f260])).

fof(f493,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK3(sK2,X0),X0) )
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f492])).

fof(f692,plain,
    ( spl7_56
    | spl7_54
    | ~ spl7_60
    | ~ spl7_22
    | ~ spl7_39
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f666,f653,f492,f259,f690,f656,f675])).

fof(f653,plain,
    ( spl7_53
  <=> sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f666,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0))
    | sK0 = k2_relat_1(sK2)
    | r2_hidden(sK3(sK2,sK0),sK0)
    | ~ spl7_22
    | ~ spl7_39
    | ~ spl7_53 ),
    inference(superposition,[],[f514,f654])).

fof(f654,plain,
    ( sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f653])).

fof(f514,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK4(sK2,X9)))
        | k2_relat_1(sK2) = X9
        | r2_hidden(sK3(sK2,X9),X9) )
    | ~ spl7_22
    | ~ spl7_39 ),
    inference(resolution,[],[f495,f80])).

fof(f658,plain,
    ( spl7_52
    | spl7_53
    | spl7_54
    | ~ spl7_22
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f629,f617,f259,f656,f653,f650])).

fof(f629,plain,
    ( sK0 = k2_relat_1(sK2)
    | sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0))
    | r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2))
    | ~ spl7_22
    | ~ spl7_46 ),
    inference(resolution,[],[f618,f260])).

fof(f619,plain,
    ( ~ spl7_5
    | spl7_46
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f615,f104,f617,f120])).

fof(f120,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f104,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f615,plain,
    ( ! [X0] :
        ( sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0))
        | r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f63,f117])).

fof(f117,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f494,plain,
    ( ~ spl7_5
    | spl7_39
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f490,f114,f104,f492,f120])).

fof(f490,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f489,f115])).

fof(f489,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | r2_hidden(sK3(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f62,f117])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f445,plain,
    ( spl7_35
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f441,f399,f265,f443])).

fof(f399,plain,
    ( spl7_34
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | k1_funct_1(sK2,sK5(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f441,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(resolution,[],[f431,f74])).

fof(f431,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(k2_relat_1(sK2),X0),sK1)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(k2_relat_1(sK2),X0),sK1)
        | r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(resolution,[],[f420,f270])).

fof(f420,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK5(sK2,sK6(k2_relat_1(sK2),X9)),sK0)
        | r2_hidden(sK6(k2_relat_1(sK2),X9),sK1)
        | r1_tarski(k2_relat_1(sK2),X9) )
    | ~ spl7_34 ),
    inference(superposition,[],[f56,f406])).

fof(f406,plain,
    ( ! [X5] :
        ( sK6(k2_relat_1(sK2),X5) = k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X5)))
        | r1_tarski(k2_relat_1(sK2),X5) )
    | ~ spl7_34 ),
    inference(resolution,[],[f400,f73])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | k1_funct_1(sK2,sK5(sK2,X0)) = X0 )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f399])).

fof(f56,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),sK1)
        | ~ r2_hidden(X3,sK0) )
    & sK0 = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK2,X3),sK1)
          | ~ r2_hidden(X3,sK0) )
      & sK0 = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f401,plain,
    ( ~ spl7_5
    | spl7_34
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f397,f104,f399,f120])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | k1_funct_1(sK2,sK5(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f92,f117])).

fof(f92,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f267,plain,
    ( ~ spl7_5
    | spl7_23
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f263,f114,f104,f265,f120])).

fof(f263,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f262,f115])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f93,f117])).

fof(f93,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f261,plain,
    ( ~ spl7_5
    | spl7_22
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f257,f114,f104,f259,f120])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f256,f115])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f91,f117])).

fof(f91,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f218,plain,
    ( spl7_17
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f210,f136,f128,f216])).

fof(f128,plain,
    ( spl7_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f136,plain,
    ( spl7_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f210,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(k2_relat_1(k1_xboole_0),X1) )
    | ~ spl7_8 ),
    inference(superposition,[],[f192,f97])).

fof(f192,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
        | r1_tarski(k2_relat_1(k1_xboole_0),X6) )
    | ~ spl7_8 ),
    inference(resolution,[],[f175,f137])).

fof(f137,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f207,plain,
    ( spl7_15
    | ~ spl7_14
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f196,f120,f201,f205])).

fof(f196,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(k2_relat_1(sK2),X1) )
    | ~ spl7_5 ),
    inference(superposition,[],[f190,f97])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f175,f121])).

fof(f121,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f154,plain,
    ( ~ spl7_5
    | spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f149,f114,f152,f120])).

fof(f149,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl7_4 ),
    inference(superposition,[],[f58,f115])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f143,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f129,f141])).

fof(f129,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f138,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f134,f136])).

fof(f134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f65,f96])).

fof(f130,plain,
    ( spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f123,f128,f125])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f99,f96])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f53,f120])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f54,f104])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f57,f110,f107,f104])).

fof(f57,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (29885)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (29893)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29877)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29897)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (29875)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (29879)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (29876)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (29883)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (29870)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29874)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (29895)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (29890)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (29892)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (29898)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (29878)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (29899)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (29882)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (29880)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (29873)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (29896)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.57  % (29891)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.61/0.57  % (29889)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.61/0.57  % (29872)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.57  % (29884)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.58  % (29871)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.61/0.58  % (29886)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.76/0.59  % (29872)Refutation not found, incomplete strategy% (29872)------------------------------
% 1.76/0.59  % (29872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (29872)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (29872)Memory used [KB]: 10746
% 1.76/0.59  % (29872)Time elapsed: 0.159 s
% 1.76/0.59  % (29872)------------------------------
% 1.76/0.59  % (29872)------------------------------
% 1.76/0.59  % (29894)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.76/0.59  % (29881)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.76/0.60  % (29888)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.76/0.60  % (29887)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.63/0.73  % (29913)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.07/0.83  % (29875)Time limit reached!
% 3.07/0.83  % (29875)------------------------------
% 3.07/0.83  % (29875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.07/0.83  % (29875)Termination reason: Time limit
% 3.07/0.83  
% 3.07/0.83  % (29875)Memory used [KB]: 8827
% 3.07/0.83  % (29875)Time elapsed: 0.410 s
% 3.07/0.83  % (29875)------------------------------
% 3.07/0.83  % (29875)------------------------------
% 4.01/0.90  % (29870)Time limit reached!
% 4.01/0.90  % (29870)------------------------------
% 4.01/0.90  % (29870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.90  % (29870)Termination reason: Time limit
% 4.01/0.90  % (29870)Termination phase: Saturation
% 4.01/0.90  
% 4.01/0.90  % (29870)Memory used [KB]: 3326
% 4.01/0.90  % (29870)Time elapsed: 0.500 s
% 4.01/0.90  % (29870)------------------------------
% 4.01/0.90  % (29870)------------------------------
% 4.01/0.92  % (29871)Time limit reached!
% 4.01/0.92  % (29871)------------------------------
% 4.01/0.92  % (29871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (29871)Termination reason: Time limit
% 4.01/0.92  % (29871)Termination phase: Saturation
% 4.01/0.92  
% 4.01/0.92  % (29871)Memory used [KB]: 7675
% 4.01/0.92  % (29871)Time elapsed: 0.500 s
% 4.01/0.92  % (29871)------------------------------
% 4.01/0.92  % (29871)------------------------------
% 4.01/0.92  % (29880)Time limit reached!
% 4.01/0.92  % (29880)------------------------------
% 4.01/0.92  % (29880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (29880)Termination reason: Time limit
% 4.01/0.92  % (29880)Termination phase: Saturation
% 4.01/0.92  
% 4.01/0.92  % (29880)Memory used [KB]: 13176
% 4.01/0.92  % (29880)Time elapsed: 0.500 s
% 4.01/0.92  % (29880)------------------------------
% 4.01/0.92  % (29880)------------------------------
% 4.01/0.93  % (29882)Time limit reached!
% 4.01/0.93  % (29882)------------------------------
% 4.01/0.93  % (29882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.93  % (29882)Termination reason: Time limit
% 4.01/0.93  
% 4.01/0.93  % (29882)Memory used [KB]: 8315
% 4.01/0.93  % (29882)Time elapsed: 0.518 s
% 4.01/0.93  % (29882)------------------------------
% 4.01/0.93  % (29882)------------------------------
% 4.34/0.93  % (29887)Time limit reached!
% 4.34/0.93  % (29887)------------------------------
% 4.34/0.93  % (29887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.93  % (29887)Termination reason: Time limit
% 4.34/0.93  % (29887)Termination phase: Saturation
% 4.34/0.93  
% 4.34/0.93  % (29887)Memory used [KB]: 14072
% 4.34/0.93  % (29887)Time elapsed: 0.500 s
% 4.34/0.93  % (29887)------------------------------
% 4.34/0.93  % (29887)------------------------------
% 4.43/0.96  % (29914)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.43/1.00  % (29915)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.85/1.01  % (29898)Time limit reached!
% 4.85/1.01  % (29898)------------------------------
% 4.85/1.01  % (29898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.01  % (29898)Termination reason: Time limit
% 4.85/1.01  % (29898)Termination phase: Saturation
% 4.85/1.01  
% 4.85/1.01  % (29898)Memory used [KB]: 7291
% 4.85/1.01  % (29898)Time elapsed: 0.600 s
% 4.85/1.01  % (29898)------------------------------
% 4.85/1.01  % (29898)------------------------------
% 4.85/1.02  % (29886)Time limit reached!
% 4.85/1.02  % (29886)------------------------------
% 4.85/1.02  % (29886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.02  % (29886)Termination reason: Time limit
% 4.85/1.02  % (29886)Termination phase: Saturation
% 4.85/1.02  
% 4.85/1.02  % (29886)Memory used [KB]: 15607
% 4.85/1.02  % (29886)Time elapsed: 0.600 s
% 4.85/1.02  % (29886)------------------------------
% 4.85/1.02  % (29886)------------------------------
% 4.85/1.04  % (29917)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.85/1.05  % (29916)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.85/1.05  % (29919)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.85/1.07  % (29918)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.85/1.08  % (29877)Time limit reached!
% 4.85/1.08  % (29877)------------------------------
% 4.85/1.08  % (29877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.08  % (29877)Termination reason: Time limit
% 5.60/1.08  
% 5.60/1.08  % (29877)Memory used [KB]: 8827
% 5.60/1.08  % (29877)Time elapsed: 0.630 s
% 5.60/1.08  % (29877)------------------------------
% 5.60/1.08  % (29877)------------------------------
% 5.60/1.12  % (29920)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.60/1.15  % (29921)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.33/1.17  % (29889)Refutation found. Thanks to Tanya!
% 6.33/1.17  % SZS status Theorem for theBenchmark
% 6.33/1.17  % SZS output start Proof for theBenchmark
% 6.33/1.18  fof(f9987,plain,(
% 6.33/1.18    $false),
% 6.33/1.18    inference(avatar_sat_refutation,[],[f112,f116,f118,f122,f130,f138,f143,f154,f207,f218,f261,f267,f401,f445,f494,f619,f658,f692,f937,f1268,f1276,f1296,f1426,f1500,f4565,f4572,f4883,f5220,f6563,f6981,f8591,f9227,f9448,f9517,f9607,f9754,f9834,f9941,f9964,f9966,f9978,f9980,f9986])).
% 6.33/1.18  fof(f9986,plain,(
% 6.33/1.18    ~spl7_15 | ~spl7_22 | ~spl7_23 | spl7_60),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9985])).
% 6.33/1.18  fof(f9985,plain,(
% 6.33/1.18    $false | (~spl7_15 | ~spl7_22 | ~spl7_23 | spl7_60)),
% 6.33/1.18    inference(resolution,[],[f691,f9849])).
% 6.33/1.18  fof(f9849,plain,(
% 6.33/1.18    ( ! [X9] : (r1_tarski(k2_relat_1(sK2),X9)) ) | (~spl7_15 | ~spl7_22 | ~spl7_23)),
% 6.33/1.18    inference(subsumption_resolution,[],[f364,f9732])).
% 6.33/1.18  fof(f9732,plain,(
% 6.33/1.18    ( ! [X8] : (r1_tarski(sK0,X8)) ) | (~spl7_15 | ~spl7_22)),
% 6.33/1.18    inference(subsumption_resolution,[],[f276,f206])).
% 6.33/1.18  fof(f206,plain,(
% 6.33/1.18    ( ! [X1] : (r1_tarski(k2_relat_1(sK2),X1)) ) | ~spl7_15),
% 6.33/1.18    inference(avatar_component_clause,[],[f205])).
% 6.33/1.18  fof(f205,plain,(
% 6.33/1.18    spl7_15 <=> ! [X1] : r1_tarski(k2_relat_1(sK2),X1)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 6.33/1.18  fof(f276,plain,(
% 6.33/1.18    ( ! [X8] : (~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK6(sK0,X8))) | r1_tarski(sK0,X8)) ) | ~spl7_22),
% 6.33/1.18    inference(resolution,[],[f268,f80])).
% 6.33/1.18  fof(f80,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f27])).
% 6.33/1.18  fof(f27,plain,(
% 6.33/1.18    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.33/1.18    inference(ennf_transformation,[],[f10])).
% 6.33/1.18  fof(f10,axiom,(
% 6.33/1.18    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 6.33/1.18  fof(f268,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK6(sK0,X0)),k2_relat_1(sK2)) | r1_tarski(sK0,X0)) ) | ~spl7_22),
% 6.33/1.18    inference(resolution,[],[f260,f73])).
% 6.33/1.18  fof(f73,plain,(
% 6.33/1.18    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f48])).
% 6.33/1.18  fof(f48,plain,(
% 6.33/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.33/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 6.33/1.18  fof(f47,plain,(
% 6.33/1.18    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 6.33/1.18    introduced(choice_axiom,[])).
% 6.33/1.18  fof(f46,plain,(
% 6.33/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.33/1.18    inference(rectify,[],[f45])).
% 6.33/1.18  fof(f45,plain,(
% 6.33/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.33/1.18    inference(nnf_transformation,[],[f26])).
% 6.33/1.18  fof(f26,plain,(
% 6.33/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.33/1.18    inference(ennf_transformation,[],[f1])).
% 6.33/1.18  fof(f1,axiom,(
% 6.33/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.33/1.18  fof(f260,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) ) | ~spl7_22),
% 6.33/1.18    inference(avatar_component_clause,[],[f259])).
% 6.33/1.18  fof(f259,plain,(
% 6.33/1.18    spl7_22 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 6.33/1.18  fof(f364,plain,(
% 6.33/1.18    ( ! [X9] : (~r1_tarski(sK0,sK5(sK2,k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X9))))) | r1_tarski(k2_relat_1(sK2),X9)) ) | (~spl7_22 | ~spl7_23)),
% 6.33/1.18    inference(resolution,[],[f334,f80])).
% 6.33/1.18  fof(f334,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK5(sK2,k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X0)))),sK0) | r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl7_22 | ~spl7_23)),
% 6.33/1.18    inference(resolution,[],[f285,f266])).
% 6.33/1.18  fof(f266,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(sK5(sK2,X0),sK0)) ) | ~spl7_23),
% 6.33/1.18    inference(avatar_component_clause,[],[f265])).
% 6.33/1.18  fof(f265,plain,(
% 6.33/1.18    spl7_23 <=> ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 6.33/1.18  fof(f285,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X0))),k2_relat_1(sK2)) | r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl7_22 | ~spl7_23)),
% 6.33/1.18    inference(resolution,[],[f270,f260])).
% 6.33/1.18  fof(f270,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK5(sK2,sK6(k2_relat_1(sK2),X0)),sK0) | r1_tarski(k2_relat_1(sK2),X0)) ) | ~spl7_23),
% 6.33/1.18    inference(resolution,[],[f266,f73])).
% 6.33/1.18  fof(f691,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0)) | spl7_60),
% 6.33/1.18    inference(avatar_component_clause,[],[f690])).
% 6.33/1.18  fof(f690,plain,(
% 6.33/1.18    spl7_60 <=> r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 6.33/1.18  fof(f9980,plain,(
% 6.33/1.18    ~spl7_15 | ~spl7_22 | spl7_278),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9979])).
% 6.33/1.18  fof(f9979,plain,(
% 6.33/1.18    $false | (~spl7_15 | ~spl7_22 | spl7_278)),
% 6.33/1.18    inference(resolution,[],[f9977,f9732])).
% 6.33/1.18  fof(f9977,plain,(
% 6.33/1.18    ~r1_tarski(sK0,sK3(sK2,sK0)) | spl7_278),
% 6.33/1.18    inference(avatar_component_clause,[],[f9976])).
% 6.33/1.18  fof(f9976,plain,(
% 6.33/1.18    spl7_278 <=> r1_tarski(sK0,sK3(sK2,sK0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).
% 6.33/1.18  fof(f9978,plain,(
% 6.33/1.18    ~spl7_278 | ~spl7_56),
% 6.33/1.18    inference(avatar_split_clause,[],[f9974,f675,f9976])).
% 6.33/1.18  fof(f675,plain,(
% 6.33/1.18    spl7_56 <=> r2_hidden(sK3(sK2,sK0),sK0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 6.33/1.18  fof(f9974,plain,(
% 6.33/1.18    ~r1_tarski(sK0,sK3(sK2,sK0)) | ~spl7_56),
% 6.33/1.18    inference(resolution,[],[f676,f80])).
% 6.33/1.18  fof(f676,plain,(
% 6.33/1.18    r2_hidden(sK3(sK2,sK0),sK0) | ~spl7_56),
% 6.33/1.18    inference(avatar_component_clause,[],[f675])).
% 6.33/1.18  fof(f9966,plain,(
% 6.33/1.18    ~spl7_15 | ~spl7_22 | ~spl7_23 | spl7_276),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9965])).
% 6.33/1.18  fof(f9965,plain,(
% 6.33/1.18    $false | (~spl7_15 | ~spl7_22 | ~spl7_23 | spl7_276)),
% 6.33/1.18    inference(resolution,[],[f9963,f9849])).
% 6.33/1.18  fof(f9963,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0))) | spl7_276),
% 6.33/1.18    inference(avatar_component_clause,[],[f9962])).
% 6.33/1.18  fof(f9962,plain,(
% 6.33/1.18    spl7_276 <=> r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).
% 6.33/1.18  fof(f9964,plain,(
% 6.33/1.18    ~spl7_276 | ~spl7_52),
% 6.33/1.18    inference(avatar_split_clause,[],[f9956,f650,f9962])).
% 6.33/1.18  fof(f650,plain,(
% 6.33/1.18    spl7_52 <=> r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 6.33/1.18  fof(f9956,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK3(sK2,sK0))) | ~spl7_52),
% 6.33/1.18    inference(resolution,[],[f651,f80])).
% 6.33/1.18  fof(f651,plain,(
% 6.33/1.18    r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2)) | ~spl7_52),
% 6.33/1.18    inference(avatar_component_clause,[],[f650])).
% 6.33/1.18  fof(f9941,plain,(
% 6.33/1.18    ~spl7_17 | spl7_91),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9940])).
% 6.33/1.18  fof(f9940,plain,(
% 6.33/1.18    $false | (~spl7_17 | spl7_91)),
% 6.33/1.18    inference(resolution,[],[f1005,f217])).
% 6.33/1.18  fof(f217,plain,(
% 6.33/1.18    ( ! [X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | ~spl7_17),
% 6.33/1.18    inference(avatar_component_clause,[],[f216])).
% 6.33/1.18  fof(f216,plain,(
% 6.33/1.18    spl7_17 <=> ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 6.33/1.18  fof(f1005,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0))) | spl7_91),
% 6.33/1.18    inference(avatar_component_clause,[],[f1004])).
% 6.33/1.18  fof(f1004,plain,(
% 6.33/1.18    spl7_91 <=> r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 6.33/1.18  fof(f9834,plain,(
% 6.33/1.18    spl7_3 | ~spl7_10 | ~spl7_35),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9833])).
% 6.33/1.18  fof(f9833,plain,(
% 6.33/1.18    $false | (spl7_3 | ~spl7_10 | ~spl7_35)),
% 6.33/1.18    inference(subsumption_resolution,[],[f158,f1427])).
% 6.33/1.18  fof(f1427,plain,(
% 6.33/1.18    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (spl7_3 | ~spl7_35)),
% 6.33/1.18    inference(resolution,[],[f111,f453])).
% 6.33/1.18  fof(f453,plain,(
% 6.33/1.18    ( ! [X8,X9] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) ) | ~spl7_35),
% 6.33/1.18    inference(resolution,[],[f444,f89])).
% 6.33/1.18  fof(f89,plain,(
% 6.33/1.18    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f33])).
% 6.33/1.18  fof(f33,plain,(
% 6.33/1.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 6.33/1.18    inference(flattening,[],[f32])).
% 6.33/1.18  fof(f32,plain,(
% 6.33/1.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 6.33/1.18    inference(ennf_transformation,[],[f13])).
% 6.33/1.18  fof(f13,axiom,(
% 6.33/1.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 6.33/1.18  fof(f444,plain,(
% 6.33/1.18    r1_tarski(k2_relat_1(sK2),sK1) | ~spl7_35),
% 6.33/1.18    inference(avatar_component_clause,[],[f443])).
% 6.33/1.18  fof(f443,plain,(
% 6.33/1.18    spl7_35 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 6.33/1.18  fof(f111,plain,(
% 6.33/1.18    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_3),
% 6.33/1.18    inference(avatar_component_clause,[],[f110])).
% 6.33/1.18  fof(f110,plain,(
% 6.33/1.18    spl7_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 6.33/1.18  fof(f158,plain,(
% 6.33/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl7_10),
% 6.33/1.18    inference(avatar_component_clause,[],[f157])).
% 6.33/1.18  fof(f157,plain,(
% 6.33/1.18    spl7_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 6.33/1.18  fof(f9754,plain,(
% 6.33/1.18    ~spl7_15 | ~spl7_22 | spl7_81),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9734])).
% 6.33/1.18  fof(f9734,plain,(
% 6.33/1.18    $false | (~spl7_15 | ~spl7_22 | spl7_81)),
% 6.33/1.18    inference(subsumption_resolution,[],[f936,f9732])).
% 6.33/1.18  fof(f936,plain,(
% 6.33/1.18    ~r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0)))) | spl7_81),
% 6.33/1.18    inference(avatar_component_clause,[],[f935])).
% 6.33/1.18  fof(f935,plain,(
% 6.33/1.18    spl7_81 <=> r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0))))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 6.33/1.18  fof(f9607,plain,(
% 6.33/1.18    spl7_49 | spl7_48 | ~spl7_17 | ~spl7_46),
% 6.33/1.18    inference(avatar_split_clause,[],[f1365,f617,f216,f635,f638])).
% 6.33/1.18  fof(f638,plain,(
% 6.33/1.18    spl7_49 <=> k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 6.33/1.18  fof(f635,plain,(
% 6.33/1.18    spl7_48 <=> sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 6.33/1.18  fof(f617,plain,(
% 6.33/1.18    spl7_46 <=> ! [X0] : (sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0)) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 6.33/1.18  fof(f1365,plain,(
% 6.33/1.18    sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0))) | k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | (~spl7_17 | ~spl7_46)),
% 6.33/1.18    inference(resolution,[],[f622,f217])).
% 6.33/1.18  fof(f622,plain,(
% 6.33/1.18    ( ! [X5] : (~r1_tarski(X5,sK3(sK2,X5)) | sK3(sK2,X5) = k1_funct_1(sK2,sK4(sK2,X5)) | k2_relat_1(sK2) = X5) ) | ~spl7_46),
% 6.33/1.18    inference(resolution,[],[f618,f80])).
% 6.33/1.18  fof(f618,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0))) ) | ~spl7_46),
% 6.33/1.18    inference(avatar_component_clause,[],[f617])).
% 6.33/1.18  fof(f9517,plain,(
% 6.33/1.18    spl7_10 | ~spl7_9),
% 6.33/1.18    inference(avatar_split_clause,[],[f9365,f152,f157])).
% 6.33/1.18  fof(f152,plain,(
% 6.33/1.18    spl7_9 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 6.33/1.18  fof(f9365,plain,(
% 6.33/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl7_9),
% 6.33/1.18    inference(resolution,[],[f76,f153])).
% 6.33/1.18  fof(f153,plain,(
% 6.33/1.18    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) | ~spl7_9),
% 6.33/1.18    inference(avatar_component_clause,[],[f152])).
% 6.33/1.18  fof(f76,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f49])).
% 6.33/1.18  fof(f49,plain,(
% 6.33/1.18    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.33/1.18    inference(nnf_transformation,[],[f4])).
% 6.33/1.18  fof(f4,axiom,(
% 6.33/1.18    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.33/1.18  fof(f9448,plain,(
% 6.33/1.18    ~spl7_91 | ~spl7_76),
% 6.33/1.18    inference(avatar_split_clause,[],[f991,f910,f1004])).
% 6.33/1.18  fof(f910,plain,(
% 6.33/1.18    spl7_76 <=> r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 6.33/1.18  fof(f991,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(k1_xboole_0),sK3(sK2,k2_relat_1(k1_xboole_0))) | ~spl7_76),
% 6.33/1.18    inference(resolution,[],[f911,f80])).
% 6.33/1.18  fof(f911,plain,(
% 6.33/1.18    r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~spl7_76),
% 6.33/1.18    inference(avatar_component_clause,[],[f910])).
% 6.33/1.18  fof(f9227,plain,(
% 6.33/1.18    ~spl7_99 | spl7_200),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f9226])).
% 6.33/1.18  fof(f9226,plain,(
% 6.33/1.18    $false | (~spl7_99 | spl7_200)),
% 6.33/1.18    inference(subsumption_resolution,[],[f6980,f1272])).
% 6.33/1.18  fof(f1272,plain,(
% 6.33/1.18    ( ! [X0] : (v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl7_99),
% 6.33/1.18    inference(avatar_component_clause,[],[f1271])).
% 6.33/1.18  fof(f1271,plain,(
% 6.33/1.18    spl7_99 <=> ! [X0] : v1_funct_2(sK2,k1_xboole_0,X0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).
% 6.33/1.18  fof(f6980,plain,(
% 6.33/1.18    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | spl7_200),
% 6.33/1.18    inference(avatar_component_clause,[],[f6979])).
% 6.33/1.18  fof(f6979,plain,(
% 6.33/1.18    spl7_200 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).
% 6.33/1.18  fof(f8591,plain,(
% 6.33/1.18    sK0 != k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relat_1(k1_xboole_0) | sK0 = k2_relat_1(k1_xboole_0)),
% 6.33/1.18    introduced(theory_tautology_sat_conflict,[])).
% 6.33/1.18  fof(f6981,plain,(
% 6.33/1.18    ~spl7_200 | ~spl7_100 | spl7_105),
% 6.33/1.18    inference(avatar_split_clause,[],[f5359,f1498,f1274,f6979])).
% 6.33/1.18  fof(f1274,plain,(
% 6.33/1.18    spl7_100 <=> k1_xboole_0 = sK0),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).
% 6.33/1.18  fof(f1498,plain,(
% 6.33/1.18    spl7_105 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 6.33/1.18  fof(f5359,plain,(
% 6.33/1.18    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_100 | spl7_105)),
% 6.33/1.18    inference(superposition,[],[f1499,f1551])).
% 6.33/1.18  fof(f1551,plain,(
% 6.33/1.18    k1_xboole_0 = sK0 | ~spl7_100),
% 6.33/1.18    inference(avatar_component_clause,[],[f1274])).
% 6.33/1.18  fof(f1499,plain,(
% 6.33/1.18    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl7_105),
% 6.33/1.18    inference(avatar_component_clause,[],[f1498])).
% 6.33/1.18  fof(f6563,plain,(
% 6.33/1.18    spl7_98 | spl7_14 | ~spl7_35 | ~spl7_104),
% 6.33/1.18    inference(avatar_split_clause,[],[f6562,f1424,f443,f201,f1259])).
% 6.33/1.18  fof(f1259,plain,(
% 6.33/1.18    spl7_98 <=> ! [X1,X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).
% 6.33/1.18  fof(f201,plain,(
% 6.33/1.18    spl7_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 6.33/1.18  fof(f1424,plain,(
% 6.33/1.18    spl7_104 <=> k1_xboole_0 = sK1),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 6.33/1.18  fof(f6562,plain,(
% 6.33/1.18    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl7_35 | ~spl7_104)),
% 6.33/1.18    inference(forward_demodulation,[],[f1464,f96])).
% 6.33/1.18  fof(f96,plain,(
% 6.33/1.18    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.33/1.18    inference(equality_resolution,[],[f79])).
% 6.33/1.18  fof(f79,plain,(
% 6.33/1.18    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 6.33/1.18    inference(cnf_transformation,[],[f51])).
% 6.33/1.18  fof(f51,plain,(
% 6.33/1.18    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.33/1.18    inference(flattening,[],[f50])).
% 6.33/1.18  fof(f50,plain,(
% 6.33/1.18    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 6.33/1.18    inference(nnf_transformation,[],[f3])).
% 6.33/1.18  fof(f3,axiom,(
% 6.33/1.18    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.33/1.18  fof(f1464,plain,(
% 6.33/1.18    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl7_35 | ~spl7_104)),
% 6.33/1.18    inference(superposition,[],[f453,f1425])).
% 6.33/1.18  fof(f1425,plain,(
% 6.33/1.18    k1_xboole_0 = sK1 | ~spl7_104),
% 6.33/1.18    inference(avatar_component_clause,[],[f1424])).
% 6.33/1.18  fof(f5220,plain,(
% 6.33/1.18    spl7_100 | ~spl7_6 | spl7_126),
% 6.33/1.18    inference(avatar_split_clause,[],[f5219,f4881,f125,f1274])).
% 6.33/1.18  fof(f125,plain,(
% 6.33/1.18    spl7_6 <=> ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 6.33/1.18  fof(f4881,plain,(
% 6.33/1.18    spl7_126 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).
% 6.33/1.18  fof(f5219,plain,(
% 6.33/1.18    k1_xboole_0 = sK0 | (~spl7_6 | spl7_126)),
% 6.33/1.18    inference(resolution,[],[f4882,f126])).
% 6.33/1.18  fof(f126,plain,(
% 6.33/1.18    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_6),
% 6.33/1.18    inference(avatar_component_clause,[],[f125])).
% 6.33/1.18  fof(f4882,plain,(
% 6.33/1.18    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl7_126),
% 6.33/1.18    inference(avatar_component_clause,[],[f4881])).
% 6.33/1.18  fof(f4883,plain,(
% 6.33/1.18    ~spl7_126 | spl7_2 | ~spl7_101 | ~spl7_104),
% 6.33/1.18    inference(avatar_split_clause,[],[f4879,f1424,f1282,f107,f4881])).
% 6.33/1.18  fof(f107,plain,(
% 6.33/1.18    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 6.33/1.18  fof(f1282,plain,(
% 6.33/1.18    spl7_101 <=> k1_xboole_0 = sK2),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).
% 6.33/1.18  fof(f4879,plain,(
% 6.33/1.18    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (spl7_2 | ~spl7_101 | ~spl7_104)),
% 6.33/1.18    inference(forward_demodulation,[],[f4633,f1425])).
% 6.33/1.18  fof(f4633,plain,(
% 6.33/1.18    ~v1_funct_2(k1_xboole_0,sK0,sK1) | (spl7_2 | ~spl7_101)),
% 6.33/1.18    inference(superposition,[],[f108,f1283])).
% 6.33/1.18  fof(f1283,plain,(
% 6.33/1.18    k1_xboole_0 = sK2 | ~spl7_101),
% 6.33/1.18    inference(avatar_component_clause,[],[f1282])).
% 6.33/1.18  fof(f108,plain,(
% 6.33/1.18    ~v1_funct_2(sK2,sK0,sK1) | spl7_2),
% 6.33/1.18    inference(avatar_component_clause,[],[f107])).
% 6.33/1.18  fof(f4572,plain,(
% 6.33/1.18    spl7_100 | ~spl7_120),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f4570])).
% 6.33/1.18  fof(f4570,plain,(
% 6.33/1.18    $false | (spl7_100 | ~spl7_120)),
% 6.33/1.18    inference(subsumption_resolution,[],[f1275,f4564])).
% 6.33/1.18  fof(f4564,plain,(
% 6.33/1.18    ( ! [X325] : (k1_xboole_0 = X325) ) | ~spl7_120),
% 6.33/1.18    inference(avatar_component_clause,[],[f4563])).
% 6.33/1.18  fof(f4563,plain,(
% 6.33/1.18    spl7_120 <=> ! [X325] : k1_xboole_0 = X325),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).
% 6.33/1.18  fof(f1275,plain,(
% 6.33/1.18    k1_xboole_0 != sK0 | spl7_100),
% 6.33/1.18    inference(avatar_component_clause,[],[f1274])).
% 6.33/1.18  fof(f4565,plain,(
% 6.33/1.18    spl7_101 | spl7_120 | ~spl7_17 | ~spl7_78 | ~spl7_103),
% 6.33/1.18    inference(avatar_split_clause,[],[f4418,f1294,f916,f216,f4563,f1282])).
% 6.33/1.18  fof(f916,plain,(
% 6.33/1.18    spl7_78 <=> sK0 = k2_relat_1(k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 6.33/1.18  fof(f1294,plain,(
% 6.33/1.18    spl7_103 <=> r1_tarski(sK2,k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 6.33/1.18  fof(f4418,plain,(
% 6.33/1.18    ( ! [X325] : (k1_xboole_0 = X325 | k1_xboole_0 = sK2) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(trivial_inequality_removal,[],[f4372])).
% 6.33/1.18  fof(f4372,plain,(
% 6.33/1.18    ( ! [X325] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X325 | k1_xboole_0 = sK2) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(superposition,[],[f77,f4242])).
% 6.33/1.18  fof(f4242,plain,(
% 6.33/1.18    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,sK2)) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f4092,f3019])).
% 6.33/1.18  fof(f3019,plain,(
% 6.33/1.18    ( ! [X5] : (m1_subset_1(k2_zfmisc_1(X5,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,sK0)))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2942,f76])).
% 6.33/1.18  fof(f2942,plain,(
% 6.33/1.18    ( ! [X99] : (r1_tarski(k2_zfmisc_1(X99,sK2),k2_zfmisc_1(X99,sK0))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(superposition,[],[f1746,f2834])).
% 6.33/1.18  fof(f2834,plain,(
% 6.33/1.18    ( ! [X12] : (sK0 = k2_relat_1(k2_zfmisc_1(X12,sK2))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2824,f1018])).
% 6.33/1.18  fof(f1018,plain,(
% 6.33/1.18    ( ! [X1] : (~r1_tarski(X1,sK0) | sK0 = X1) ) | (~spl7_17 | ~spl7_78)),
% 6.33/1.18    inference(superposition,[],[f219,f917])).
% 6.33/1.18  fof(f917,plain,(
% 6.33/1.18    sK0 = k2_relat_1(k1_xboole_0) | ~spl7_78),
% 6.33/1.18    inference(avatar_component_clause,[],[f916])).
% 6.33/1.18  fof(f219,plain,(
% 6.33/1.18    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X0) ) | ~spl7_17),
% 6.33/1.18    inference(resolution,[],[f217,f71])).
% 6.33/1.18  fof(f71,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f44])).
% 6.33/1.18  fof(f44,plain,(
% 6.33/1.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.33/1.18    inference(flattening,[],[f43])).
% 6.33/1.18  fof(f43,plain,(
% 6.33/1.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.33/1.18    inference(nnf_transformation,[],[f2])).
% 6.33/1.18  fof(f2,axiom,(
% 6.33/1.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.33/1.18  fof(f2824,plain,(
% 6.33/1.18    ( ! [X10] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X10,sK2)),sK0)) ) | (~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2809,f141])).
% 6.33/1.18  fof(f141,plain,(
% 6.33/1.18    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 6.33/1.18    inference(resolution,[],[f76,f94])).
% 6.33/1.18  fof(f94,plain,(
% 6.33/1.18    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.33/1.18    inference(equality_resolution,[],[f70])).
% 6.33/1.18  fof(f70,plain,(
% 6.33/1.18    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.33/1.18    inference(cnf_transformation,[],[f44])).
% 6.33/1.18  fof(f2809,plain,(
% 6.33/1.18    ( ! [X6,X4,X5] : (~m1_subset_1(k2_zfmisc_1(X4,sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | r1_tarski(k2_relat_1(k2_zfmisc_1(X4,sK2)),sK0)) ) | (~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2401,f191])).
% 6.33/1.18  fof(f191,plain,(
% 6.33/1.18    ( ! [X4,X2,X5,X3] : (~m1_subset_1(k2_zfmisc_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X5,X4))) | r1_tarski(k2_relat_1(k2_zfmisc_1(X2,X3)),X4)) )),
% 6.33/1.18    inference(resolution,[],[f175,f65])).
% 6.33/1.18  fof(f65,plain,(
% 6.33/1.18    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f6])).
% 6.33/1.18  fof(f6,axiom,(
% 6.33/1.18    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 6.33/1.18  fof(f175,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 6.33/1.18    inference(resolution,[],[f82,f66])).
% 6.33/1.18  fof(f66,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f42])).
% 6.33/1.18  fof(f42,plain,(
% 6.33/1.18    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.33/1.18    inference(nnf_transformation,[],[f23])).
% 6.33/1.18  fof(f23,plain,(
% 6.33/1.18    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.33/1.18    inference(ennf_transformation,[],[f5])).
% 6.33/1.18  fof(f5,axiom,(
% 6.33/1.18    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 6.33/1.18  fof(f82,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f29])).
% 6.33/1.18  fof(f29,plain,(
% 6.33/1.18    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.33/1.18    inference(ennf_transformation,[],[f17])).
% 6.33/1.18  fof(f17,plain,(
% 6.33/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 6.33/1.18    inference(pure_predicate_removal,[],[f11])).
% 6.33/1.18  fof(f11,axiom,(
% 6.33/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.33/1.18  fof(f2401,plain,(
% 6.33/1.18    ( ! [X14,X15,X13,X16] : (m1_subset_1(k2_zfmisc_1(X13,sK2),k1_zfmisc_1(k2_zfmisc_1(X16,sK0))) | ~m1_subset_1(k2_zfmisc_1(X13,sK2),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))) ) | (~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2209,f76])).
% 6.33/1.18  fof(f2209,plain,(
% 6.33/1.18    ( ! [X6,X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,sK2),k2_zfmisc_1(X6,sK0)) | ~m1_subset_1(k2_zfmisc_1(X3,sK2),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2206,f1851])).
% 6.33/1.18  fof(f1851,plain,(
% 6.33/1.18    ( ! [X17,X18] : (~r1_tarski(X17,k1_xboole_0) | r1_tarski(X17,k2_zfmisc_1(X18,sK0))) ) | ~spl7_78),
% 6.33/1.18    inference(resolution,[],[f1823,f1811])).
% 6.33/1.18  fof(f1811,plain,(
% 6.33/1.18    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,sK0))) ) | ~spl7_78),
% 6.33/1.18    inference(forward_demodulation,[],[f1807,f917])).
% 6.33/1.18  fof(f1807,plain,(
% 6.33/1.18    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k2_relat_1(k1_xboole_0)))) )),
% 6.33/1.18    inference(superposition,[],[f1746,f96])).
% 6.33/1.18  fof(f1823,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(X0,X1) | ~r1_tarski(X0,X2)) )),
% 6.33/1.18    inference(duplicate_literal_removal,[],[f1817])).
% 6.33/1.18  fof(f1817,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(resolution,[],[f185,f73])).
% 6.33/1.18  fof(f185,plain,(
% 6.33/1.18    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK6(X4,X3),X5) | r1_tarski(X4,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,X2)) )),
% 6.33/1.18    inference(resolution,[],[f174,f72])).
% 6.33/1.18  fof(f72,plain,(
% 6.33/1.18    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f48])).
% 6.33/1.18  fof(f174,plain,(
% 6.33/1.18    ( ! [X4,X5,X3] : (~r2_hidden(sK6(X3,X4),X5) | ~r1_tarski(X5,X4) | r1_tarski(X3,X4)) )),
% 6.33/1.18    inference(resolution,[],[f72,f74])).
% 6.33/1.18  fof(f74,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f48])).
% 6.33/1.18  fof(f2206,plain,(
% 6.33/1.18    ( ! [X8,X7,X9] : (r1_tarski(k2_zfmisc_1(X7,sK2),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(X7,sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))) ) | ~spl7_103),
% 6.33/1.18    inference(resolution,[],[f1976,f75])).
% 6.33/1.18  fof(f75,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f49])).
% 6.33/1.18  fof(f1976,plain,(
% 6.33/1.18    ( ! [X2,X3,X1] : (m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl7_103),
% 6.33/1.18    inference(forward_demodulation,[],[f1968,f96])).
% 6.33/1.18  fof(f1968,plain,(
% 6.33/1.18    ( ! [X2,X3,X1] : (m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,k1_xboole_0))) | ~m1_subset_1(k2_zfmisc_1(X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl7_103),
% 6.33/1.18    inference(resolution,[],[f1942,f89])).
% 6.33/1.18  fof(f1942,plain,(
% 6.33/1.18    ( ! [X47] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X47,sK2)),k1_xboole_0)) ) | ~spl7_103),
% 6.33/1.18    inference(resolution,[],[f1903,f1860])).
% 6.33/1.18  fof(f1860,plain,(
% 6.33/1.18    ( ! [X34] : (~r1_tarski(X34,sK2) | r1_tarski(X34,k1_xboole_0)) ) | ~spl7_103),
% 6.33/1.18    inference(resolution,[],[f1823,f1295])).
% 6.33/1.18  fof(f1295,plain,(
% 6.33/1.18    r1_tarski(sK2,k1_xboole_0) | ~spl7_103),
% 6.33/1.18    inference(avatar_component_clause,[],[f1294])).
% 6.33/1.18  fof(f1903,plain,(
% 6.33/1.18    ( ! [X12,X13] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X12,X13)),X13)) )),
% 6.33/1.18    inference(resolution,[],[f191,f141])).
% 6.33/1.18  fof(f1746,plain,(
% 6.33/1.18    ( ! [X4,X5] : (r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_relat_1(k2_zfmisc_1(X4,X5))))) )),
% 6.33/1.18    inference(resolution,[],[f1238,f141])).
% 6.33/1.18  fof(f1238,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(X0,k2_zfmisc_1(X1,k2_relat_1(X0)))) )),
% 6.33/1.18    inference(resolution,[],[f433,f75])).
% 6.33/1.18  fof(f433,plain,(
% 6.33/1.18    ( ! [X4,X5,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,k2_relat_1(X3)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 6.33/1.18    inference(resolution,[],[f89,f94])).
% 6.33/1.18  fof(f4092,plain,(
% 6.33/1.18    ( ! [X12,X13,X11] : (~m1_subset_1(k2_zfmisc_1(X11,sK2),k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | k1_xboole_0 = k2_zfmisc_1(X11,sK2)) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(subsumption_resolution,[],[f2211,f4087])).
% 6.33/1.18  fof(f4087,plain,(
% 6.33/1.18    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X2))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f4083,f1815])).
% 6.33/1.18  fof(f1815,plain,(
% 6.33/1.18    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) ) | ~spl7_78),
% 6.33/1.18    inference(resolution,[],[f1811,f76])).
% 6.33/1.18  fof(f4083,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(superposition,[],[f4069,f97])).
% 6.33/1.18  fof(f97,plain,(
% 6.33/1.18    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.33/1.18    inference(equality_resolution,[],[f78])).
% 6.33/1.18  fof(f78,plain,(
% 6.33/1.18    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 6.33/1.18    inference(cnf_transformation,[],[f51])).
% 6.33/1.18  fof(f4069,plain,(
% 6.33/1.18    ( ! [X21,X19,X20,X18] : (r1_tarski(k2_zfmisc_1(X18,sK2),k2_zfmisc_1(X19,X21)) | ~m1_subset_1(k2_zfmisc_1(X18,sK2),k1_zfmisc_1(k2_zfmisc_1(X19,X20)))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2844,f75])).
% 6.33/1.18  fof(f2844,plain,(
% 6.33/1.18    ( ! [X4,X2,X5,X3] : (m1_subset_1(k2_zfmisc_1(X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(k2_zfmisc_1(X2,sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X5)))) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2833,f89])).
% 6.33/1.18  fof(f2833,plain,(
% 6.33/1.18    ( ! [X10,X11] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X10,sK2)),X11)) ) | (~spl7_17 | ~spl7_78 | ~spl7_103)),
% 6.33/1.18    inference(resolution,[],[f2824,f1020])).
% 6.33/1.18  fof(f1020,plain,(
% 6.33/1.18    ( ! [X4,X3] : (~r1_tarski(X3,sK0) | r1_tarski(X3,X4)) ) | (~spl7_17 | ~spl7_78)),
% 6.33/1.18    inference(superposition,[],[f222,f917])).
% 6.33/1.18  fof(f222,plain,(
% 6.33/1.18    ( ! [X4,X3] : (~r1_tarski(X3,k2_relat_1(k1_xboole_0)) | r1_tarski(X3,X4)) ) | ~spl7_17),
% 6.33/1.18    inference(resolution,[],[f217,f177])).
% 6.33/1.18  fof(f177,plain,(
% 6.33/1.18    ( ! [X4,X2,X3] : (~r1_tarski(X3,sK6(X2,X4)) | ~r1_tarski(X2,X3) | r1_tarski(X2,X4)) )),
% 6.33/1.18    inference(resolution,[],[f173,f73])).
% 6.33/1.18  fof(f173,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X2,X0)) )),
% 6.33/1.18    inference(resolution,[],[f72,f80])).
% 6.33/1.18  fof(f2211,plain,(
% 6.33/1.18    ( ! [X12,X13,X11] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X11,sK2)) | k1_xboole_0 = k2_zfmisc_1(X11,sK2) | ~m1_subset_1(k2_zfmisc_1(X11,sK2),k1_zfmisc_1(k2_zfmisc_1(X12,X13)))) ) | ~spl7_103),
% 6.33/1.18    inference(resolution,[],[f2206,f71])).
% 6.33/1.18  fof(f77,plain,(
% 6.33/1.18    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 6.33/1.18    inference(cnf_transformation,[],[f51])).
% 6.33/1.18  fof(f1500,plain,(
% 6.33/1.18    ~spl7_105 | spl7_2 | ~spl7_104),
% 6.33/1.18    inference(avatar_split_clause,[],[f1440,f1424,f107,f1498])).
% 6.33/1.18  fof(f1440,plain,(
% 6.33/1.18    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (spl7_2 | ~spl7_104)),
% 6.33/1.18    inference(superposition,[],[f108,f1425])).
% 6.33/1.18  fof(f1426,plain,(
% 6.33/1.18    ~spl7_3 | spl7_104 | spl7_2 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f1419,f114,f107,f1424,f110])).
% 6.33/1.18  fof(f114,plain,(
% 6.33/1.18    spl7_4 <=> sK0 = k1_relat_1(sK2)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 6.33/1.18  fof(f1419,plain,(
% 6.33/1.18    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl7_2 | ~spl7_4)),
% 6.33/1.18    inference(resolution,[],[f1418,f108])).
% 6.33/1.18  fof(f1418,plain,(
% 6.33/1.18    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl7_4),
% 6.33/1.18    inference(equality_resolution,[],[f1416])).
% 6.33/1.18  fof(f1416,plain,(
% 6.33/1.18    ( ! [X0,X1] : (sK0 != X0 | v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_4),
% 6.33/1.18    inference(superposition,[],[f572,f115])).
% 6.33/1.18  fof(f115,plain,(
% 6.33/1.18    sK0 = k1_relat_1(sK2) | ~spl7_4),
% 6.33/1.18    inference(avatar_component_clause,[],[f114])).
% 6.33/1.18  fof(f572,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(duplicate_literal_removal,[],[f571])).
% 6.33/1.18  fof(f571,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(superposition,[],[f85,f81])).
% 6.33/1.18  fof(f81,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f28])).
% 6.33/1.18  fof(f28,plain,(
% 6.33/1.18    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.33/1.18    inference(ennf_transformation,[],[f12])).
% 6.33/1.18  fof(f12,axiom,(
% 6.33/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 6.33/1.18  fof(f85,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f52])).
% 6.33/1.18  fof(f52,plain,(
% 6.33/1.18    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.33/1.18    inference(nnf_transformation,[],[f31])).
% 6.33/1.18  fof(f31,plain,(
% 6.33/1.18    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.33/1.18    inference(flattening,[],[f30])).
% 6.33/1.18  fof(f30,plain,(
% 6.33/1.18    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.33/1.18    inference(ennf_transformation,[],[f14])).
% 6.33/1.18  fof(f14,axiom,(
% 6.33/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 6.33/1.18  fof(f1296,plain,(
% 6.33/1.18    spl7_103 | ~spl7_14),
% 6.33/1.18    inference(avatar_split_clause,[],[f1292,f201,f1294])).
% 6.33/1.18  fof(f1292,plain,(
% 6.33/1.18    r1_tarski(sK2,k1_xboole_0) | ~spl7_14),
% 6.33/1.18    inference(resolution,[],[f1261,f75])).
% 6.33/1.18  fof(f1261,plain,(
% 6.33/1.18    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_14),
% 6.33/1.18    inference(avatar_component_clause,[],[f201])).
% 6.33/1.18  fof(f1276,plain,(
% 6.33/1.18    spl7_99 | ~spl7_14 | ~spl7_100 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f1186,f114,f1274,f201,f1271])).
% 6.33/1.18  fof(f1186,plain,(
% 6.33/1.18    ( ! [X0] : (k1_xboole_0 != sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl7_4),
% 6.33/1.18    inference(superposition,[],[f333,f115])).
% 6.33/1.18  fof(f333,plain,(
% 6.33/1.18    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 6.33/1.18    inference(duplicate_literal_removal,[],[f332])).
% 6.33/1.18  fof(f332,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 6.33/1.18    inference(forward_demodulation,[],[f331,f97])).
% 6.33/1.18  fof(f331,plain,(
% 6.33/1.18    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 6.33/1.18    inference(superposition,[],[f132,f81])).
% 6.33/1.18  fof(f132,plain,(
% 6.33/1.18    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 6.33/1.18    inference(forward_demodulation,[],[f101,f97])).
% 6.33/1.18  fof(f101,plain,(
% 6.33/1.18    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.33/1.18    inference(equality_resolution,[],[f86])).
% 6.33/1.18  fof(f86,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f52])).
% 6.33/1.18  fof(f1268,plain,(
% 6.33/1.18    ~spl7_10 | ~spl7_98),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f1264])).
% 6.33/1.18  fof(f1264,plain,(
% 6.33/1.18    $false | (~spl7_10 | ~spl7_98)),
% 6.33/1.18    inference(subsumption_resolution,[],[f158,f1260])).
% 6.33/1.18  fof(f1260,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl7_98),
% 6.33/1.18    inference(avatar_component_clause,[],[f1259])).
% 6.33/1.18  fof(f937,plain,(
% 6.33/1.18    spl7_76 | ~spl7_81 | spl7_78 | ~spl7_22 | ~spl7_23 | ~spl7_39 | ~spl7_48 | ~spl7_54),
% 6.33/1.18    inference(avatar_split_clause,[],[f933,f656,f635,f492,f265,f259,f916,f935,f910])).
% 6.33/1.18  fof(f492,plain,(
% 6.33/1.18    spl7_39 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 6.33/1.18  fof(f656,plain,(
% 6.33/1.18    spl7_54 <=> sK0 = k2_relat_1(sK2)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 6.33/1.18  fof(f933,plain,(
% 6.33/1.18    sK0 = k2_relat_1(k1_xboole_0) | ~r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0)))) | r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl7_22 | ~spl7_23 | ~spl7_39 | ~spl7_48 | ~spl7_54)),
% 6.33/1.18    inference(forward_demodulation,[],[f900,f657])).
% 6.33/1.18  fof(f657,plain,(
% 6.33/1.18    sK0 = k2_relat_1(sK2) | ~spl7_54),
% 6.33/1.18    inference(avatar_component_clause,[],[f656])).
% 6.33/1.18  fof(f900,plain,(
% 6.33/1.18    ~r1_tarski(sK0,sK5(sK2,sK3(sK2,k2_relat_1(k1_xboole_0)))) | r2_hidden(sK3(sK2,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | (~spl7_22 | ~spl7_23 | ~spl7_39 | ~spl7_48)),
% 6.33/1.18    inference(superposition,[],[f550,f636])).
% 6.33/1.18  fof(f636,plain,(
% 6.33/1.18    sK3(sK2,k2_relat_1(k1_xboole_0)) = k1_funct_1(sK2,sK4(sK2,k2_relat_1(k1_xboole_0))) | ~spl7_48),
% 6.33/1.18    inference(avatar_component_clause,[],[f635])).
% 6.33/1.18  fof(f550,plain,(
% 6.33/1.18    ( ! [X9] : (~r1_tarski(sK0,sK5(sK2,k1_funct_1(sK2,sK4(sK2,X9)))) | r2_hidden(sK3(sK2,X9),X9) | k2_relat_1(sK2) = X9) ) | (~spl7_22 | ~spl7_23 | ~spl7_39)),
% 6.33/1.18    inference(resolution,[],[f510,f80])).
% 6.33/1.18  fof(f510,plain,(
% 6.33/1.18    ( ! [X1] : (r2_hidden(sK5(sK2,k1_funct_1(sK2,sK4(sK2,X1))),sK0) | k2_relat_1(sK2) = X1 | r2_hidden(sK3(sK2,X1),X1)) ) | (~spl7_22 | ~spl7_23 | ~spl7_39)),
% 6.33/1.18    inference(resolution,[],[f495,f266])).
% 6.33/1.18  fof(f495,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK4(sK2,X0)),k2_relat_1(sK2)) | r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl7_22 | ~spl7_39)),
% 6.33/1.18    inference(resolution,[],[f493,f260])).
% 6.33/1.18  fof(f493,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k2_relat_1(sK2) = X0 | r2_hidden(sK3(sK2,X0),X0)) ) | ~spl7_39),
% 6.33/1.18    inference(avatar_component_clause,[],[f492])).
% 6.33/1.18  fof(f692,plain,(
% 6.33/1.18    spl7_56 | spl7_54 | ~spl7_60 | ~spl7_22 | ~spl7_39 | ~spl7_53),
% 6.33/1.18    inference(avatar_split_clause,[],[f666,f653,f492,f259,f690,f656,f675])).
% 6.33/1.18  fof(f653,plain,(
% 6.33/1.18    spl7_53 <=> sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 6.33/1.18  fof(f666,plain,(
% 6.33/1.18    ~r1_tarski(k2_relat_1(sK2),sK3(sK2,sK0)) | sK0 = k2_relat_1(sK2) | r2_hidden(sK3(sK2,sK0),sK0) | (~spl7_22 | ~spl7_39 | ~spl7_53)),
% 6.33/1.18    inference(superposition,[],[f514,f654])).
% 6.33/1.18  fof(f654,plain,(
% 6.33/1.18    sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0)) | ~spl7_53),
% 6.33/1.18    inference(avatar_component_clause,[],[f653])).
% 6.33/1.18  fof(f514,plain,(
% 6.33/1.18    ( ! [X9] : (~r1_tarski(k2_relat_1(sK2),k1_funct_1(sK2,sK4(sK2,X9))) | k2_relat_1(sK2) = X9 | r2_hidden(sK3(sK2,X9),X9)) ) | (~spl7_22 | ~spl7_39)),
% 6.33/1.18    inference(resolution,[],[f495,f80])).
% 6.33/1.18  fof(f658,plain,(
% 6.33/1.18    spl7_52 | spl7_53 | spl7_54 | ~spl7_22 | ~spl7_46),
% 6.33/1.18    inference(avatar_split_clause,[],[f629,f617,f259,f656,f653,f650])).
% 6.33/1.18  fof(f629,plain,(
% 6.33/1.18    sK0 = k2_relat_1(sK2) | sK3(sK2,sK0) = k1_funct_1(sK2,sK4(sK2,sK0)) | r2_hidden(k1_funct_1(sK2,sK3(sK2,sK0)),k2_relat_1(sK2)) | (~spl7_22 | ~spl7_46)),
% 6.33/1.18    inference(resolution,[],[f618,f260])).
% 6.33/1.18  fof(f619,plain,(
% 6.33/1.18    ~spl7_5 | spl7_46 | ~spl7_1),
% 6.33/1.18    inference(avatar_split_clause,[],[f615,f104,f617,f120])).
% 6.33/1.18  fof(f120,plain,(
% 6.33/1.18    spl7_5 <=> v1_relat_1(sK2)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 6.33/1.18  fof(f104,plain,(
% 6.33/1.18    spl7_1 <=> v1_funct_1(sK2)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 6.33/1.18  fof(f615,plain,(
% 6.33/1.18    ( ! [X0] : (sK3(sK2,X0) = k1_funct_1(sK2,sK4(sK2,X0)) | r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 6.33/1.18    inference(resolution,[],[f63,f117])).
% 6.33/1.18  fof(f117,plain,(
% 6.33/1.18    v1_funct_1(sK2) | ~spl7_1),
% 6.33/1.18    inference(avatar_component_clause,[],[f104])).
% 6.33/1.18  fof(f63,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~v1_funct_1(X0) | sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f41])).
% 6.33/1.18  fof(f41,plain,(
% 6.33/1.18    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.33/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f40,f39,f38])).
% 6.33/1.18  fof(f38,plain,(
% 6.33/1.18    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 6.33/1.18    introduced(choice_axiom,[])).
% 6.33/1.18  fof(f39,plain,(
% 6.33/1.18    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 6.33/1.18    introduced(choice_axiom,[])).
% 6.33/1.18  fof(f40,plain,(
% 6.33/1.18    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 6.33/1.18    introduced(choice_axiom,[])).
% 6.33/1.18  fof(f37,plain,(
% 6.33/1.18    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.33/1.18    inference(rectify,[],[f36])).
% 6.33/1.18  fof(f36,plain,(
% 6.33/1.18    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.33/1.18    inference(nnf_transformation,[],[f22])).
% 6.33/1.18  fof(f22,plain,(
% 6.33/1.18    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.33/1.18    inference(flattening,[],[f21])).
% 6.33/1.18  fof(f21,plain,(
% 6.33/1.18    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.33/1.18    inference(ennf_transformation,[],[f9])).
% 6.33/1.18  fof(f9,axiom,(
% 6.33/1.18    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 6.33/1.18  fof(f494,plain,(
% 6.33/1.18    ~spl7_5 | spl7_39 | ~spl7_1 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f490,f114,f104,f492,f120])).
% 6.33/1.18  fof(f490,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | (~spl7_1 | ~spl7_4)),
% 6.33/1.18    inference(forward_demodulation,[],[f489,f115])).
% 6.33/1.18  fof(f489,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK3(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 6.33/1.18    inference(resolution,[],[f62,f117])).
% 6.33/1.18  fof(f62,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f41])).
% 6.33/1.18  fof(f445,plain,(
% 6.33/1.18    spl7_35 | ~spl7_23 | ~spl7_34),
% 6.33/1.18    inference(avatar_split_clause,[],[f441,f399,f265,f443])).
% 6.33/1.18  fof(f399,plain,(
% 6.33/1.18    spl7_34 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,X0)) = X0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 6.33/1.18  fof(f441,plain,(
% 6.33/1.18    r1_tarski(k2_relat_1(sK2),sK1) | (~spl7_23 | ~spl7_34)),
% 6.33/1.18    inference(duplicate_literal_removal,[],[f435])).
% 6.33/1.18  fof(f435,plain,(
% 6.33/1.18    r1_tarski(k2_relat_1(sK2),sK1) | r1_tarski(k2_relat_1(sK2),sK1) | (~spl7_23 | ~spl7_34)),
% 6.33/1.18    inference(resolution,[],[f431,f74])).
% 6.33/1.18  fof(f431,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK2),X0),sK1) | r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl7_23 | ~spl7_34)),
% 6.33/1.18    inference(duplicate_literal_removal,[],[f429])).
% 6.33/1.18  fof(f429,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK2),X0),sK1) | r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl7_23 | ~spl7_34)),
% 6.33/1.18    inference(resolution,[],[f420,f270])).
% 6.33/1.18  fof(f420,plain,(
% 6.33/1.18    ( ! [X9] : (~r2_hidden(sK5(sK2,sK6(k2_relat_1(sK2),X9)),sK0) | r2_hidden(sK6(k2_relat_1(sK2),X9),sK1) | r1_tarski(k2_relat_1(sK2),X9)) ) | ~spl7_34),
% 6.33/1.18    inference(superposition,[],[f56,f406])).
% 6.33/1.18  fof(f406,plain,(
% 6.33/1.18    ( ! [X5] : (sK6(k2_relat_1(sK2),X5) = k1_funct_1(sK2,sK5(sK2,sK6(k2_relat_1(sK2),X5))) | r1_tarski(k2_relat_1(sK2),X5)) ) | ~spl7_34),
% 6.33/1.18    inference(resolution,[],[f400,f73])).
% 6.33/1.18  fof(f400,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,X0)) = X0) ) | ~spl7_34),
% 6.33/1.18    inference(avatar_component_clause,[],[f399])).
% 6.33/1.18  fof(f56,plain,(
% 6.33/1.18    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f35])).
% 6.33/1.18  fof(f35,plain,(
% 6.33/1.18    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 6.33/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34])).
% 6.33/1.18  fof(f34,plain,(
% 6.33/1.18    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),sK1) | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 6.33/1.18    introduced(choice_axiom,[])).
% 6.33/1.18  fof(f19,plain,(
% 6.33/1.18    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & ! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 6.33/1.18    inference(flattening,[],[f18])).
% 6.33/1.18  fof(f18,plain,(
% 6.33/1.18    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & (! [X3] : (r2_hidden(k1_funct_1(X2,X3),X1) | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 6.33/1.18    inference(ennf_transformation,[],[f16])).
% 6.33/1.18  fof(f16,negated_conjecture,(
% 6.33/1.18    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.33/1.18    inference(negated_conjecture,[],[f15])).
% 6.33/1.18  fof(f15,conjecture,(
% 6.33/1.18    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 6.33/1.18  fof(f401,plain,(
% 6.33/1.18    ~spl7_5 | spl7_34 | ~spl7_1),
% 6.33/1.18    inference(avatar_split_clause,[],[f397,f104,f399,f120])).
% 6.33/1.18  fof(f397,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | k1_funct_1(sK2,sK5(sK2,X0)) = X0 | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 6.33/1.18    inference(resolution,[],[f92,f117])).
% 6.33/1.18  fof(f92,plain,(
% 6.33/1.18    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK5(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(equality_resolution,[],[f60])).
% 6.33/1.18  fof(f60,plain,(
% 6.33/1.18    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f41])).
% 6.33/1.18  fof(f267,plain,(
% 6.33/1.18    ~spl7_5 | spl7_23 | ~spl7_1 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f263,f114,f104,f265,f120])).
% 6.33/1.18  fof(f263,plain,(
% 6.33/1.18    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl7_1 | ~spl7_4)),
% 6.33/1.18    inference(forward_demodulation,[],[f262,f115])).
% 6.33/1.18  fof(f262,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 6.33/1.18    inference(resolution,[],[f93,f117])).
% 6.33/1.18  fof(f93,plain,(
% 6.33/1.18    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(equality_resolution,[],[f59])).
% 6.33/1.18  fof(f59,plain,(
% 6.33/1.18    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f41])).
% 6.33/1.18  fof(f261,plain,(
% 6.33/1.18    ~spl7_5 | spl7_22 | ~spl7_1 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f257,f114,f104,f259,f120])).
% 6.33/1.18  fof(f257,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl7_1 | ~spl7_4)),
% 6.33/1.18    inference(forward_demodulation,[],[f256,f115])).
% 6.33/1.18  fof(f256,plain,(
% 6.33/1.18    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 6.33/1.18    inference(resolution,[],[f91,f117])).
% 6.33/1.18  fof(f91,plain,(
% 6.33/1.18    ( ! [X6,X0] : (~v1_funct_1(X0) | ~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(equality_resolution,[],[f90])).
% 6.33/1.18  fof(f90,plain,(
% 6.33/1.18    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(equality_resolution,[],[f61])).
% 6.33/1.18  fof(f61,plain,(
% 6.33/1.18    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f41])).
% 6.33/1.18  fof(f218,plain,(
% 6.33/1.18    spl7_17 | ~spl7_7 | ~spl7_8),
% 6.33/1.18    inference(avatar_split_clause,[],[f210,f136,f128,f216])).
% 6.33/1.18  fof(f128,plain,(
% 6.33/1.18    spl7_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 6.33/1.18  fof(f136,plain,(
% 6.33/1.18    spl7_8 <=> v1_relat_1(k1_xboole_0)),
% 6.33/1.18    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 6.33/1.18  fof(f210,plain,(
% 6.33/1.18    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | ~spl7_8),
% 6.33/1.18    inference(superposition,[],[f192,f97])).
% 6.33/1.18  fof(f192,plain,(
% 6.33/1.18    ( ! [X6,X7] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | r1_tarski(k2_relat_1(k1_xboole_0),X6)) ) | ~spl7_8),
% 6.33/1.18    inference(resolution,[],[f175,f137])).
% 6.33/1.18  fof(f137,plain,(
% 6.33/1.18    v1_relat_1(k1_xboole_0) | ~spl7_8),
% 6.33/1.18    inference(avatar_component_clause,[],[f136])).
% 6.33/1.18  fof(f207,plain,(
% 6.33/1.18    spl7_15 | ~spl7_14 | ~spl7_5),
% 6.33/1.18    inference(avatar_split_clause,[],[f196,f120,f201,f205])).
% 6.33/1.18  fof(f196,plain,(
% 6.33/1.18    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK2),X1)) ) | ~spl7_5),
% 6.33/1.18    inference(superposition,[],[f190,f97])).
% 6.33/1.18  fof(f190,plain,(
% 6.33/1.18    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r1_tarski(k2_relat_1(sK2),X0)) ) | ~spl7_5),
% 6.33/1.18    inference(resolution,[],[f175,f121])).
% 6.33/1.18  fof(f121,plain,(
% 6.33/1.18    v1_relat_1(sK2) | ~spl7_5),
% 6.33/1.18    inference(avatar_component_clause,[],[f120])).
% 6.33/1.18  fof(f154,plain,(
% 6.33/1.18    ~spl7_5 | spl7_9 | ~spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f149,f114,f152,f120])).
% 6.33/1.18  fof(f149,plain,(
% 6.33/1.18    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) | ~v1_relat_1(sK2) | ~spl7_4),
% 6.33/1.18    inference(superposition,[],[f58,f115])).
% 6.33/1.18  fof(f58,plain,(
% 6.33/1.18    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 6.33/1.18    inference(cnf_transformation,[],[f20])).
% 6.33/1.18  fof(f20,plain,(
% 6.33/1.18    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.33/1.18    inference(ennf_transformation,[],[f8])).
% 6.33/1.18  fof(f8,axiom,(
% 6.33/1.18    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 6.33/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 6.33/1.18  fof(f143,plain,(
% 6.33/1.18    spl7_7),
% 6.33/1.18    inference(avatar_contradiction_clause,[],[f142])).
% 6.33/1.18  fof(f142,plain,(
% 6.33/1.18    $false | spl7_7),
% 6.33/1.18    inference(subsumption_resolution,[],[f129,f141])).
% 6.33/1.18  fof(f129,plain,(
% 6.33/1.18    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl7_7),
% 6.33/1.18    inference(avatar_component_clause,[],[f128])).
% 6.33/1.18  fof(f138,plain,(
% 6.33/1.18    spl7_8),
% 6.33/1.18    inference(avatar_split_clause,[],[f134,f136])).
% 6.33/1.18  fof(f134,plain,(
% 6.33/1.18    v1_relat_1(k1_xboole_0)),
% 6.33/1.18    inference(superposition,[],[f65,f96])).
% 6.33/1.18  fof(f130,plain,(
% 6.33/1.18    spl7_6 | ~spl7_7),
% 6.33/1.18    inference(avatar_split_clause,[],[f123,f128,f125])).
% 6.33/1.18  fof(f123,plain,(
% 6.33/1.18    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 6.33/1.18    inference(forward_demodulation,[],[f99,f96])).
% 6.33/1.18  fof(f99,plain,(
% 6.33/1.18    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.33/1.18    inference(equality_resolution,[],[f98])).
% 6.33/1.18  fof(f98,plain,(
% 6.33/1.18    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(equality_resolution,[],[f88])).
% 6.33/1.18  fof(f88,plain,(
% 6.33/1.18    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.33/1.18    inference(cnf_transformation,[],[f52])).
% 6.33/1.18  fof(f122,plain,(
% 6.33/1.18    spl7_5),
% 6.33/1.18    inference(avatar_split_clause,[],[f53,f120])).
% 6.33/1.18  fof(f53,plain,(
% 6.33/1.18    v1_relat_1(sK2)),
% 6.33/1.18    inference(cnf_transformation,[],[f35])).
% 6.33/1.18  fof(f118,plain,(
% 6.33/1.18    spl7_1),
% 6.33/1.18    inference(avatar_split_clause,[],[f54,f104])).
% 6.33/1.18  fof(f54,plain,(
% 6.33/1.18    v1_funct_1(sK2)),
% 6.33/1.18    inference(cnf_transformation,[],[f35])).
% 6.33/1.18  fof(f116,plain,(
% 6.33/1.18    spl7_4),
% 6.33/1.18    inference(avatar_split_clause,[],[f55,f114])).
% 6.33/1.18  fof(f55,plain,(
% 6.33/1.18    sK0 = k1_relat_1(sK2)),
% 6.33/1.18    inference(cnf_transformation,[],[f35])).
% 6.33/1.18  fof(f112,plain,(
% 6.33/1.18    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 6.33/1.18    inference(avatar_split_clause,[],[f57,f110,f107,f104])).
% 6.33/1.18  fof(f57,plain,(
% 6.33/1.18    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 6.33/1.18    inference(cnf_transformation,[],[f35])).
% 6.33/1.18  % SZS output end Proof for theBenchmark
% 6.33/1.18  % (29889)------------------------------
% 6.33/1.18  % (29889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.33/1.18  % (29889)Termination reason: Refutation
% 6.33/1.18  
% 6.33/1.18  % (29889)Memory used [KB]: 15223
% 6.33/1.18  % (29889)Time elapsed: 0.763 s
% 6.33/1.18  % (29889)------------------------------
% 6.33/1.18  % (29889)------------------------------
% 6.33/1.19  % (29869)Success in time 0.821 s
%------------------------------------------------------------------------------

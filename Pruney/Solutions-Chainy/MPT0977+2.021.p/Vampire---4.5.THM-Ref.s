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
% DateTime   : Thu Dec  3 13:01:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 254 expanded)
%              Number of leaves         :   43 ( 116 expanded)
%              Depth                    :    7
%              Number of atoms          :  475 ( 714 expanded)
%              Number of equality atoms :   57 (  82 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f65,f69,f74,f81,f99,f107,f115,f119,f130,f141,f149,f156,f164,f170,f179,f187,f193,f202,f216,f227,f235,f248,f254,f266,f270,f276,f279,f283])).

fof(f283,plain,
    ( ~ spl3_25
    | spl3_34
    | ~ spl3_35
    | ~ spl3_42 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl3_25
    | spl3_34
    | ~ spl3_35
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f281,f231])).

fof(f231,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_35
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f281,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_25
    | spl3_34
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f280,f178])).

fof(f178,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl3_25
  <=> sK2 = k8_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f280,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)
    | spl3_34
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f226,f265])).

fof(f265,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_42
  <=> ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f226,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_34
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f279,plain,
    ( ~ spl3_2
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f60,f234])).

fof(f234,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl3_36
  <=> ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f60,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f276,plain,
    ( ~ spl3_2
    | ~ spl3_29
    | spl3_33
    | ~ spl3_35
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_29
    | spl3_33
    | ~ spl3_35
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f274,f231])).

fof(f274,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_2
    | ~ spl3_29
    | spl3_33
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f273,f201])).

fof(f201,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_29
  <=> sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f273,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ spl3_2
    | spl3_33
    | ~ spl3_43 ),
    inference(backward_demodulation,[],[f222,f271])).

fof(f271,plain,
    ( ! [X0] : k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2)
    | ~ spl3_2
    | ~ spl3_43 ),
    inference(resolution,[],[f269,f60])).

fof(f269,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_43
  <=> ! [X3,X5,X4,X6] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f222,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_33
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f270,plain,
    ( spl3_43
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f250,f246,f63,f268])).

fof(f63,plain,
    ( spl3_3
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f246,plain,
    ( spl3_39
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f250,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3) )
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(resolution,[],[f247,f64])).

fof(f64,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f247,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f246])).

fof(f266,plain,
    ( spl3_42
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f257,f252,f154,f63,f264])).

fof(f154,plain,
    ( spl3_21
  <=> ! [X3] : k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f252,plain,
    ( spl3_40
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f257,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_3
    | ~ spl3_21
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f256,f155])).

fof(f155,plain,
    ( ! [X3] : k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f256,plain,
    ( ! [X0] : k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))
    | ~ spl3_3
    | ~ spl3_40 ),
    inference(resolution,[],[f253,f64])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl3_40
    | ~ spl3_2
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f249,f246,f58,f252])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) )
    | ~ spl3_2
    | ~ spl3_39 ),
    inference(resolution,[],[f247,f60])).

fof(f248,plain,(
    spl3_39 ),
    inference(avatar_split_clause,[],[f50,f246])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f235,plain,
    ( spl3_35
    | spl3_36
    | ~ spl3_2
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f217,f214,f58,f233,f229])).

fof(f214,plain,
    ( spl3_32
  <=> ! [X1,X3,X0,X2] :
        ( r2_relset_1(X0,X1,X2,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | r2_relset_1(sK0,sK1,sK2,sK2) )
    | ~ spl3_2
    | ~ spl3_32 ),
    inference(resolution,[],[f215,f60])).

fof(f215,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_relset_1(X0,X1,X2,X2) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f214])).

fof(f227,plain,
    ( ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f35,f224,f220])).

fof(f35,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f216,plain,(
    spl3_32 ),
    inference(avatar_split_clause,[],[f49,f214])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f202,plain,
    ( spl3_29
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f196,f191,f127,f78,f199])).

fof(f78,plain,
    ( spl3_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f127,plain,
    ( spl3_16
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f191,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_partfun1(X0),X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f196,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),sK2)
    | ~ spl3_6
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f194,f80])).

fof(f80,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f194,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(k6_partfun1(sK0),sK2)
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(resolution,[],[f192,f129])).

fof(f129,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(k6_partfun1(X0),X1) = X1 )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl3_28
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f189,f185,f97,f191])).

fof(f97,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f185,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_partfun1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k6_partfun1(X0),X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0) )
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(k6_partfun1(X0),X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_10
    | ~ spl3_27 ),
    inference(resolution,[],[f186,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_partfun1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f52,f185])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f179,plain,
    ( spl3_25
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f173,f168,f138,f78,f176])).

fof(f138,plain,
    ( spl3_18
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f168,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f173,plain,
    ( sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_6
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f171,f80])).

fof(f171,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK1,sK2)
    | ~ spl3_18
    | ~ spl3_24 ),
    inference(resolution,[],[f169,f140])).

fof(f140,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl3_24
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f166,f162,f105,f168])).

fof(f105,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0) )
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f163,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f41,f162])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f156,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f151,f147,f78,f154])).

fof(f147,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f151,plain,
    ( ! [X3] : k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f148,f80])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f51,f147])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f141,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f135,f117,f58,f138])).

fof(f117,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f135,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(resolution,[],[f118,f60])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f130,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f124,f113,f58,f127])).

fof(f113,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f124,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f114,f60])).

fof(f114,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f113])).

fof(f119,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f47,f113])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f99,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f81,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f72,f58,f78])).

fof(f72,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f73,f60])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f70,f67,f54,f72])).

fof(f54,plain,
    ( spl3_1
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f63])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f61,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f39,f54])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (24238)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.43  % (24245)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (24245)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f286,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f56,f61,f65,f69,f74,f81,f99,f107,f115,f119,f130,f141,f149,f156,f164,f170,f179,f187,f193,f202,f216,f227,f235,f248,f254,f266,f270,f276,f279,f283])).
% 0.21/0.43  fof(f283,plain,(
% 0.21/0.43    ~spl3_25 | spl3_34 | ~spl3_35 | ~spl3_42),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f282])).
% 0.21/0.43  fof(f282,plain,(
% 0.21/0.43    $false | (~spl3_25 | spl3_34 | ~spl3_35 | ~spl3_42)),
% 0.21/0.43    inference(subsumption_resolution,[],[f281,f231])).
% 0.21/0.43  fof(f231,plain,(
% 0.21/0.43    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_35),
% 0.21/0.43    inference(avatar_component_clause,[],[f229])).
% 0.21/0.43  fof(f229,plain,(
% 0.21/0.43    spl3_35 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.43  fof(f281,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl3_25 | spl3_34 | ~spl3_42)),
% 0.21/0.43    inference(forward_demodulation,[],[f280,f178])).
% 0.21/0.43  fof(f178,plain,(
% 0.21/0.43    sK2 = k8_relat_1(sK1,sK2) | ~spl3_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f176])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    spl3_25 <=> sK2 = k8_relat_1(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.43  fof(f280,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) | (spl3_34 | ~spl3_42)),
% 0.21/0.43    inference(forward_demodulation,[],[f226,f265])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | ~spl3_42),
% 0.21/0.43    inference(avatar_component_clause,[],[f264])).
% 0.21/0.43  fof(f264,plain,(
% 0.21/0.43    spl3_42 <=> ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.43  fof(f226,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_34),
% 0.21/0.43    inference(avatar_component_clause,[],[f224])).
% 0.21/0.43  fof(f224,plain,(
% 0.21/0.43    spl3_34 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.43  fof(f279,plain,(
% 0.21/0.43    ~spl3_2 | ~spl3_36),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.43  fof(f278,plain,(
% 0.21/0.43    $false | (~spl3_2 | ~spl3_36)),
% 0.21/0.43    inference(subsumption_resolution,[],[f60,f234])).
% 0.21/0.43  fof(f234,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl3_36),
% 0.21/0.43    inference(avatar_component_clause,[],[f233])).
% 0.21/0.43  fof(f233,plain,(
% 0.21/0.43    spl3_36 <=> ! [X0] : ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f58])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f276,plain,(
% 0.21/0.43    ~spl3_2 | ~spl3_29 | spl3_33 | ~spl3_35 | ~spl3_43),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.43  fof(f275,plain,(
% 0.21/0.43    $false | (~spl3_2 | ~spl3_29 | spl3_33 | ~spl3_35 | ~spl3_43)),
% 0.21/0.43    inference(subsumption_resolution,[],[f274,f231])).
% 0.21/0.43  fof(f274,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl3_2 | ~spl3_29 | spl3_33 | ~spl3_43)),
% 0.21/0.43    inference(forward_demodulation,[],[f273,f201])).
% 0.21/0.43  fof(f201,plain,(
% 0.21/0.43    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) | ~spl3_29),
% 0.21/0.43    inference(avatar_component_clause,[],[f199])).
% 0.21/0.43  fof(f199,plain,(
% 0.21/0.43    spl3_29 <=> sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.43  fof(f273,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | (~spl3_2 | spl3_33 | ~spl3_43)),
% 0.21/0.43    inference(backward_demodulation,[],[f222,f271])).
% 0.21/0.43  fof(f271,plain,(
% 0.21/0.43    ( ! [X0] : (k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) = k5_relat_1(k6_partfun1(X0),sK2)) ) | (~spl3_2 | ~spl3_43)),
% 0.21/0.43    inference(resolution,[],[f269,f60])).
% 0.21/0.43  fof(f269,plain,(
% 0.21/0.43    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3)) ) | ~spl3_43),
% 0.21/0.43    inference(avatar_component_clause,[],[f268])).
% 0.21/0.43  fof(f268,plain,(
% 0.21/0.43    spl3_43 <=> ! [X3,X5,X4,X6] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.43  fof(f222,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_33),
% 0.21/0.43    inference(avatar_component_clause,[],[f220])).
% 0.21/0.43  fof(f220,plain,(
% 0.21/0.43    spl3_33 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.43  fof(f270,plain,(
% 0.21/0.43    spl3_43 | ~spl3_3 | ~spl3_39),
% 0.21/0.43    inference(avatar_split_clause,[],[f250,f246,f63,f268])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl3_3 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f246,plain,(
% 0.21/0.43    spl3_39 <=> ! [X1,X3,X5,X0,X2,X4] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.43  fof(f250,plain,(
% 0.21/0.43    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(X6,X6,X4,X5,k6_partfun1(X6),X3) = k5_relat_1(k6_partfun1(X6),X3)) ) | (~spl3_3 | ~spl3_39)),
% 0.21/0.43    inference(resolution,[],[f247,f64])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f247,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) ) | ~spl3_39),
% 0.21/0.43    inference(avatar_component_clause,[],[f246])).
% 0.21/0.43  fof(f266,plain,(
% 0.21/0.43    spl3_42 | ~spl3_3 | ~spl3_21 | ~spl3_40),
% 0.21/0.43    inference(avatar_split_clause,[],[f257,f252,f154,f63,f264])).
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    spl3_21 <=> ! [X3] : k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.43  fof(f252,plain,(
% 0.21/0.43    spl3_40 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.43  fof(f257,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | (~spl3_3 | ~spl3_21 | ~spl3_40)),
% 0.21/0.43    inference(forward_demodulation,[],[f256,f155])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    ( ! [X3] : (k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))) ) | ~spl3_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f154])).
% 0.21/0.43  fof(f256,plain,(
% 0.21/0.43    ( ! [X0] : (k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) ) | (~spl3_3 | ~spl3_40)),
% 0.21/0.43    inference(resolution,[],[f253,f64])).
% 0.21/0.43  fof(f253,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) ) | ~spl3_40),
% 0.21/0.43    inference(avatar_component_clause,[],[f252])).
% 0.21/0.43  fof(f254,plain,(
% 0.21/0.43    spl3_40 | ~spl3_2 | ~spl3_39),
% 0.21/0.43    inference(avatar_split_clause,[],[f249,f246,f58,f252])).
% 0.21/0.43  fof(f249,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k4_relset_1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) ) | (~spl3_2 | ~spl3_39)),
% 0.21/0.43    inference(resolution,[],[f247,f60])).
% 0.21/0.43  fof(f248,plain,(
% 0.21/0.43    spl3_39),
% 0.21/0.43    inference(avatar_split_clause,[],[f50,f246])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    spl3_35 | spl3_36 | ~spl3_2 | ~spl3_32),
% 0.21/0.43    inference(avatar_split_clause,[],[f217,f214,f58,f233,f229])).
% 0.21/0.43  fof(f214,plain,(
% 0.21/0.43    spl3_32 <=> ! [X1,X3,X0,X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.43  fof(f217,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_relset_1(sK0,sK1,sK2,sK2)) ) | (~spl3_2 | ~spl3_32)),
% 0.21/0.43    inference(resolution,[],[f215,f60])).
% 0.21/0.43  fof(f215,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) | ~spl3_32),
% 0.21/0.43    inference(avatar_component_clause,[],[f214])).
% 0.21/0.43  fof(f227,plain,(
% 0.21/0.43    ~spl3_33 | ~spl3_34),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f224,f220])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.21/0.43    inference(negated_conjecture,[],[f13])).
% 0.21/0.43  fof(f13,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 0.21/0.43  fof(f216,plain,(
% 0.21/0.43    spl3_32),
% 0.21/0.43    inference(avatar_split_clause,[],[f49,f214])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(flattening,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.43  fof(f202,plain,(
% 0.21/0.43    spl3_29 | ~spl3_6 | ~spl3_16 | ~spl3_28),
% 0.21/0.43    inference(avatar_split_clause,[],[f196,f191,f127,f78,f199])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl3_6 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    spl3_16 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    spl3_28 <=> ! [X1,X0] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) | (~spl3_6 | ~spl3_16 | ~spl3_28)),
% 0.21/0.43    inference(subsumption_resolution,[],[f194,f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f78])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | sK2 = k5_relat_1(k6_partfun1(sK0),sK2) | (~spl3_16 | ~spl3_28)),
% 0.21/0.43    inference(resolution,[],[f192,f129])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    v4_relat_1(sK2,sK0) | ~spl3_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f127])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k5_relat_1(k6_partfun1(X0),X1) = X1) ) | ~spl3_28),
% 0.21/0.43    inference(avatar_component_clause,[],[f191])).
% 0.21/0.43  fof(f193,plain,(
% 0.21/0.43    spl3_28 | ~spl3_10 | ~spl3_27),
% 0.21/0.43    inference(avatar_split_clause,[],[f189,f185,f97,f191])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl3_10 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f185,plain,(
% 0.21/0.43    spl3_27 <=> ! [X1,X0] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) ) | (~spl3_10 | ~spl3_27)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | (~spl3_10 | ~spl3_27)),
% 0.21/0.43    inference(resolution,[],[f186,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f97])).
% 0.21/0.43  fof(f186,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_partfun1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_27),
% 0.21/0.43    inference(avatar_component_clause,[],[f185])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    spl3_27),
% 0.21/0.43    inference(avatar_split_clause,[],[f52,f185])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f42,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.43  fof(f179,plain,(
% 0.21/0.43    spl3_25 | ~spl3_6 | ~spl3_18 | ~spl3_24),
% 0.21/0.43    inference(avatar_split_clause,[],[f173,f168,f138,f78,f176])).
% 0.21/0.43  fof(f138,plain,(
% 0.21/0.43    spl3_18 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.43  fof(f168,plain,(
% 0.21/0.43    spl3_24 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    sK2 = k8_relat_1(sK1,sK2) | (~spl3_6 | ~spl3_18 | ~spl3_24)),
% 0.21/0.43    inference(subsumption_resolution,[],[f171,f80])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK1,sK2) | (~spl3_18 | ~spl3_24)),
% 0.21/0.43    inference(resolution,[],[f169,f140])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    v5_relat_1(sK2,sK1) | ~spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f169,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) ) | ~spl3_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f168])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    spl3_24 | ~spl3_12 | ~spl3_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f166,f162,f105,f168])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl3_12 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl3_23 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.44  fof(f166,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) ) | (~spl3_12 | ~spl3_23)),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | (~spl3_12 | ~spl3_23)),
% 0.21/0.44    inference(resolution,[],[f163,f106])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f105])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) ) | ~spl3_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f162])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    spl3_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f41,f162])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    spl3_21 | ~spl3_6 | ~spl3_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f151,f147,f78,f154])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl3_20 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    ( ! [X3] : (k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))) ) | (~spl3_6 | ~spl3_20)),
% 0.21/0.44    inference(resolution,[],[f148,f80])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))) ) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f147])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl3_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f51,f147])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f40,f36])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl3_18 | ~spl3_2 | ~spl3_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f135,f117,f58,f138])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl3_15 <=> ! [X1,X0,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    v5_relat_1(sK2,sK1) | (~spl3_2 | ~spl3_15)),
% 0.21/0.44    inference(resolution,[],[f118,f60])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) ) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f117])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_16 | ~spl3_2 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f124,f113,f58,f127])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    spl3_14 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    v4_relat_1(sK2,sK0) | (~spl3_2 | ~spl3_14)),
% 0.21/0.44    inference(resolution,[],[f114,f60])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f113])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    spl3_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f117])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f47,f113])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f105])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl3_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f43,f97])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl3_6 | ~spl3_2 | ~spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f72,f58,f78])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl3_5 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    v1_relat_1(sK2) | (~spl3_2 | ~spl3_5)),
% 0.21/0.44    inference(resolution,[],[f73,f60])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl3_5 | ~spl3_1 | ~spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f70,f67,f54,f72])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl3_1 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl3_4 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | (~spl3_1 | ~spl3_4)),
% 0.21/0.44    inference(resolution,[],[f68,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f67])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f63])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.44    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f54])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (24245)------------------------------
% 0.21/0.44  % (24245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (24245)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (24245)Memory used [KB]: 6268
% 0.21/0.44  % (24245)Time elapsed: 0.053 s
% 0.21/0.44  % (24245)------------------------------
% 0.21/0.44  % (24245)------------------------------
% 0.21/0.44  % (24237)Success in time 0.08 s
%------------------------------------------------------------------------------

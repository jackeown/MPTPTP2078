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
% DateTime   : Thu Dec  3 12:57:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 236 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          :  571 (1169 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f91,f103,f109,f135,f137,f161,f164,f524,f538,f547,f553,f573,f584])).

fof(f584,plain,
    ( ~ spl12_11
    | ~ spl12_8
    | ~ spl12_10
    | spl12_60 ),
    inference(avatar_split_clause,[],[f578,f571,f133,f107,f149])).

fof(f149,plain,
    ( spl12_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f107,plain,
    ( spl12_8
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f133,plain,
    ( spl12_10
  <=> ! [X7,X8] :
        ( ~ r2_hidden(k4_tarski(X7,X8),sK3)
        | r2_hidden(X7,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f571,plain,
    ( spl12_60
  <=> r2_hidden(sK11(sK4,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_60])])).

fof(f578,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl12_10
    | spl12_60 ),
    inference(resolution,[],[f576,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2)
            & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK11(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2)
        & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f576,plain,
    ( ! [X6] : ~ r2_hidden(k4_tarski(sK11(sK4,sK1,sK3),X6),sK3)
    | ~ spl12_10
    | spl12_60 ),
    inference(resolution,[],[f572,f134])).

fof(f134,plain,
    ( ! [X8,X7] :
        ( r2_hidden(X7,sK2)
        | ~ r2_hidden(k4_tarski(X7,X8),sK3) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f572,plain,
    ( ~ r2_hidden(sK11(sK4,sK1,sK3),sK2)
    | spl12_60 ),
    inference(avatar_component_clause,[],[f571])).

fof(f573,plain,
    ( ~ spl12_11
    | ~ spl12_60
    | ~ spl12_8
    | ~ spl12_58 ),
    inference(avatar_split_clause,[],[f569,f551,f107,f571,f149])).

fof(f551,plain,
    ( spl12_58
  <=> ! [X0] :
        ( ~ m1_subset_1(sK11(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK11(sK4,X0,sK3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f569,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK11(sK4,sK1,sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl12_58 ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ r2_hidden(sK11(sK4,sK1,sK3),sK2)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl12_58 ),
    inference(resolution,[],[f564,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f564,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK11(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK11(sK4,X0,sK3),sK2) )
    | ~ spl12_58 ),
    inference(resolution,[],[f552,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f552,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK11(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK11(sK4,X0,sK3),sK1) )
    | ~ spl12_58 ),
    inference(avatar_component_clause,[],[f551])).

fof(f553,plain,
    ( ~ spl12_11
    | spl12_58
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f548,f80,f551,f149])).

fof(f80,plain,
    ( spl12_2
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(k4_tarski(X5,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f548,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK11(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK11(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl12_2 ),
    inference(resolution,[],[f81,f66])).

fof(f81,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f547,plain,
    ( ~ spl12_7
    | spl12_8
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f545,f77,f107,f101])).

fof(f101,plain,
    ( spl12_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f77,plain,
    ( spl12_1
  <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f545,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl12_1 ),
    inference(superposition,[],[f83,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f83,plain,
    ( r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f538,plain,
    ( ~ spl12_4
    | spl12_54 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl12_4
    | spl12_54 ),
    inference(subsumption_resolution,[],[f90,f535])).

fof(f535,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5,X0),sK3)
    | spl12_54 ),
    inference(resolution,[],[f523,f74])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK8(X0,X1),X3),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f523,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl12_54 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl12_54
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl12_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f524,plain,
    ( ~ spl12_3
    | ~ spl12_54
    | ~ spl12_4
    | ~ spl12_7
    | spl12_8 ),
    inference(avatar_split_clause,[],[f517,f107,f101,f89,f522,f85])).

fof(f85,plain,
    ( spl12_3
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f517,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK1)
    | ~ spl12_4
    | ~ spl12_7
    | spl12_8 ),
    inference(resolution,[],[f515,f90])).

fof(f515,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(X5,sK4),sK3)
        | ~ r2_hidden(X5,k1_relat_1(sK3))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl12_7
    | spl12_8 ),
    inference(resolution,[],[f513,f108])).

fof(f108,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | spl12_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f513,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(X7,k9_relat_1(sK3,X8))
        | ~ r2_hidden(X6,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X6,X7),sK3)
        | ~ r2_hidden(X6,X8) )
    | ~ spl12_7 ),
    inference(resolution,[],[f466,f102])).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f466,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X1,k9_relat_1(X2,X3))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r2_hidden(k4_tarski(X5,X7),X8)
      | ~ r2_hidden(X5,k1_relat_1(X8))
      | r2_hidden(X7,k9_relat_1(X8,X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f164,plain,(
    spl12_13 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl12_13 ),
    inference(resolution,[],[f160,f58])).

fof(f160,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl12_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl12_13
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f161,plain,
    ( ~ spl12_13
    | ~ spl12_7
    | spl12_11 ),
    inference(avatar_split_clause,[],[f156,f149,f101,f159])).

fof(f156,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl12_7
    | spl12_11 ),
    inference(resolution,[],[f155,f102])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl12_11 ),
    inference(resolution,[],[f150,f51])).

fof(f150,plain,
    ( ~ v1_relat_1(sK3)
    | spl12_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f137,plain,
    ( ~ spl12_7
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f102,f131])).

fof(f131,plain,
    ( ! [X10,X9] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl12_9
  <=> ! [X9,X10] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f135,plain,
    ( spl12_9
    | spl12_10
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f128,f101,f133,f130])).

fof(f128,plain,
    ( ! [X10,X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X7,X8),sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | r2_hidden(X7,sK2) )
    | ~ spl12_7 ),
    inference(resolution,[],[f125,f102])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | r2_hidden(X0,X3) ) ),
    inference(resolution,[],[f116,f58])).

fof(f116,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ v1_relat_1(X11)
      | ~ r2_hidden(k4_tarski(X6,X8),X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(X11))
      | r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f114,f51])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f113,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f73,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f109,plain,
    ( ~ spl12_7
    | ~ spl12_8
    | spl12_1 ),
    inference(avatar_split_clause,[],[f104,f77,f107,f101])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl12_1 ),
    inference(superposition,[],[f78,f70])).

fof(f78,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f103,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ! [X5] :
          ( ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
          | ~ m1_subset_1(X5,sK2) )
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & ( ( r2_hidden(sK5,sK1)
        & r2_hidden(k4_tarski(sK5,sK4),sK3)
        & m1_subset_1(sK5,sK2) )
      | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ! [X5] :
                  ( ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(k4_tarski(X5,X4),X3)
                  | ~ m1_subset_1(X5,X2) )
              | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & ( ? [X6] :
                  ( r2_hidden(X6,X1)
                  & r2_hidden(k4_tarski(X6,X4),X3)
                  & m1_subset_1(X6,X2) )
              | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
            & m1_subset_1(X4,X0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(k4_tarski(X5,X4),sK3)
                | ~ m1_subset_1(X5,sK2) )
            | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,sK1)
                & r2_hidden(k4_tarski(X6,X4),sK3)
                & m1_subset_1(X6,sK2) )
            | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4] :
        ( ( ! [X5] :
              ( ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(k4_tarski(X5,X4),sK3)
              | ~ m1_subset_1(X5,sK2) )
          | ~ r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & ( ? [X6] :
              ( r2_hidden(X6,sK1)
              & r2_hidden(k4_tarski(X6,X4),sK3)
              & m1_subset_1(X6,sK2) )
          | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1)) )
        & m1_subset_1(X4,sK0) )
   => ( ( ! [X5] :
            ( ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
            | ~ m1_subset_1(X5,sK2) )
        | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & ( ? [X6] :
            ( r2_hidden(X6,sK1)
            & r2_hidden(k4_tarski(X6,sK4),sK3)
            & m1_subset_1(X6,sK2) )
        | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) )
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X6] :
        ( r2_hidden(X6,sK1)
        & r2_hidden(k4_tarski(X6,sK4),sK3)
        & m1_subset_1(X6,sK2) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(k4_tarski(sK5,sK4),sK3)
      & m1_subset_1(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X6] :
                ( r2_hidden(X6,X1)
                & r2_hidden(k4_tarski(X6,X4),X3)
                & m1_subset_1(X6,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(X5,X1)
                | ~ r2_hidden(k4_tarski(X5,X4),X3)
                | ~ m1_subset_1(X5,X2) )
            | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) )
            | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
          <~> ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X4),X3)
                & m1_subset_1(X5,X2) ) )
          & m1_subset_1(X4,X0) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ! [X4] :
            ( m1_subset_1(X4,X0)
           => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
            <=> ? [X5] :
                  ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X5,X4),X3)
                  & m1_subset_1(X5,X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f91,plain,
    ( spl12_1
    | spl12_4 ),
    inference(avatar_split_clause,[],[f48,f89,f77])).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f49,f85,f77])).

fof(f49,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f50,f80,f77])).

fof(f50,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(k4_tarski(X5,sK4),sK3)
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (2864)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.43  % (2857)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.43  % (2864)Refutation not found, incomplete strategy% (2864)------------------------------
% 0.22/0.43  % (2864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (2864)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (2864)Memory used [KB]: 1663
% 0.22/0.43  % (2864)Time elapsed: 0.037 s
% 0.22/0.43  % (2864)------------------------------
% 0.22/0.43  % (2864)------------------------------
% 0.22/0.46  % (2857)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f589,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f82,f87,f91,f103,f109,f135,f137,f161,f164,f524,f538,f547,f553,f573,f584])).
% 0.22/0.47  fof(f584,plain,(
% 0.22/0.47    ~spl12_11 | ~spl12_8 | ~spl12_10 | spl12_60),
% 0.22/0.47    inference(avatar_split_clause,[],[f578,f571,f133,f107,f149])).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    spl12_11 <=> v1_relat_1(sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    spl12_8 <=> r2_hidden(sK4,k9_relat_1(sK3,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl12_10 <=> ! [X7,X8] : (~r2_hidden(k4_tarski(X7,X8),sK3) | r2_hidden(X7,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.22/0.47  fof(f571,plain,(
% 0.22/0.47    spl12_60 <=> r2_hidden(sK11(sK4,sK1,sK3),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_60])])).
% 0.22/0.47  fof(f578,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | (~spl12_10 | spl12_60)),
% 0.22/0.47    inference(resolution,[],[f576,f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2) & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f42,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK11(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK11(X0,X1,X2),X0),X2) & r2_hidden(sK11(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(rectify,[],[f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(nnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.47  fof(f576,plain,(
% 0.22/0.47    ( ! [X6] : (~r2_hidden(k4_tarski(sK11(sK4,sK1,sK3),X6),sK3)) ) | (~spl12_10 | spl12_60)),
% 0.22/0.47    inference(resolution,[],[f572,f134])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ( ! [X8,X7] : (r2_hidden(X7,sK2) | ~r2_hidden(k4_tarski(X7,X8),sK3)) ) | ~spl12_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f133])).
% 0.22/0.47  fof(f572,plain,(
% 0.22/0.47    ~r2_hidden(sK11(sK4,sK1,sK3),sK2) | spl12_60),
% 0.22/0.47    inference(avatar_component_clause,[],[f571])).
% 0.22/0.47  fof(f573,plain,(
% 0.22/0.47    ~spl12_11 | ~spl12_60 | ~spl12_8 | ~spl12_58),
% 0.22/0.47    inference(avatar_split_clause,[],[f569,f551,f107,f571,f149])).
% 0.22/0.47  fof(f551,plain,(
% 0.22/0.47    spl12_58 <=> ! [X0] : (~m1_subset_1(sK11(sK4,X0,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK11(sK4,X0,sK3),sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).
% 0.22/0.47  fof(f569,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK11(sK4,sK1,sK3),sK2) | ~v1_relat_1(sK3) | ~spl12_58),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f568])).
% 0.22/0.47  fof(f568,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~r2_hidden(sK11(sK4,sK1,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl12_58),
% 0.22/0.47    inference(resolution,[],[f564,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f44])).
% 0.22/0.47  fof(f564,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(sK11(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK11(sK4,X0,sK3),sK2)) ) | ~spl12_58),
% 0.22/0.47    inference(resolution,[],[f552,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.47  fof(f552,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK11(sK4,X0,sK3),sK2) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK11(sK4,X0,sK3),sK1)) ) | ~spl12_58),
% 0.22/0.47    inference(avatar_component_clause,[],[f551])).
% 0.22/0.47  fof(f553,plain,(
% 0.22/0.47    ~spl12_11 | spl12_58 | ~spl12_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f548,f80,f551,f149])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl12_2 <=> ! [X5] : (~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(X5,sK4),sK3))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.22/0.47  fof(f548,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK11(sK4,X0,sK3),sK2) | ~r2_hidden(sK11(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) ) | ~spl12_2),
% 0.22/0.47    inference(resolution,[],[f81,f66])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl12_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f547,plain,(
% 0.22/0.47    ~spl12_7 | spl12_8 | ~spl12_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f545,f77,f107,f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl12_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl12_1 <=> r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.22/0.47  fof(f545,plain,(
% 0.22/0.47    r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl12_1),
% 0.22/0.47    inference(superposition,[],[f83,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | ~spl12_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f538,plain,(
% 0.22/0.47    ~spl12_4 | spl12_54),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f537])).
% 0.22/0.47  fof(f537,plain,(
% 0.22/0.47    $false | (~spl12_4 | spl12_54)),
% 0.22/0.47    inference(subsumption_resolution,[],[f90,f535])).
% 0.22/0.47  fof(f535,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK5,X0),sK3)) ) | spl12_54),
% 0.22/0.47    inference(resolution,[],[f523,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f36,f39,f38,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK8(X0,X1),X3),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK8(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK9(X0,X1)),X0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK10(X0,X5)),X0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.47    inference(rectify,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.47  fof(f523,plain,(
% 0.22/0.47    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl12_54),
% 0.22/0.47    inference(avatar_component_clause,[],[f522])).
% 0.22/0.47  fof(f522,plain,(
% 0.22/0.47    spl12_54 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl12_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl12_4 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.22/0.47  fof(f524,plain,(
% 0.22/0.47    ~spl12_3 | ~spl12_54 | ~spl12_4 | ~spl12_7 | spl12_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f517,f107,f101,f89,f522,f85])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    spl12_3 <=> r2_hidden(sK5,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.22/0.47  fof(f517,plain,(
% 0.22/0.47    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~r2_hidden(sK5,sK1) | (~spl12_4 | ~spl12_7 | spl12_8)),
% 0.22/0.47    inference(resolution,[],[f515,f90])).
% 0.22/0.47  fof(f515,plain,(
% 0.22/0.47    ( ! [X5] : (~r2_hidden(k4_tarski(X5,sK4),sK3) | ~r2_hidden(X5,k1_relat_1(sK3)) | ~r2_hidden(X5,sK1)) ) | (~spl12_7 | spl12_8)),
% 0.22/0.47    inference(resolution,[],[f513,f108])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | spl12_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f107])).
% 0.22/0.47  fof(f513,plain,(
% 0.22/0.47    ( ! [X6,X8,X7] : (r2_hidden(X7,k9_relat_1(sK3,X8)) | ~r2_hidden(X6,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X6,X7),sK3) | ~r2_hidden(X6,X8)) ) | ~spl12_7),
% 0.22/0.47    inference(resolution,[],[f466,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl12_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f101])).
% 0.22/0.47  fof(f466,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X1,k9_relat_1(X2,X3)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X0,X3)) )),
% 0.22/0.47    inference(resolution,[],[f119,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    ( ! [X6,X8,X7,X5,X9] : (~v1_relat_1(X9) | ~r2_hidden(k4_tarski(X5,X7),X8) | ~r2_hidden(X5,k1_relat_1(X8)) | r2_hidden(X7,k9_relat_1(X8,X6)) | ~m1_subset_1(X8,k1_zfmisc_1(X9)) | ~r2_hidden(X5,X6)) )),
% 0.22/0.47    inference(resolution,[],[f68,f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f44])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    spl12_13),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    $false | spl12_13),
% 0.22/0.47    inference(resolution,[],[f160,f58])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl12_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f159])).
% 0.22/0.47  fof(f159,plain,(
% 0.22/0.47    spl12_13 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ~spl12_13 | ~spl12_7 | spl12_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f156,f149,f101,f159])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl12_7 | spl12_11)),
% 0.22/0.47    inference(resolution,[],[f155,f102])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl12_11),
% 0.22/0.47    inference(resolution,[],[f150,f51])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    ~v1_relat_1(sK3) | spl12_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f149])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ~spl12_7 | ~spl12_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    $false | (~spl12_7 | ~spl12_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f102,f131])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ( ! [X10,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))) ) | ~spl12_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f130])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    spl12_9 <=> ! [X9,X10] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    spl12_9 | spl12_10 | ~spl12_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f128,f101,f133,f130])).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ( ! [X10,X8,X7,X9] : (~r2_hidden(k4_tarski(X7,X8),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | r2_hidden(X7,sK2)) ) | ~spl12_7),
% 0.22/0.47    inference(resolution,[],[f125,f102])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | r2_hidden(X0,X3)) )),
% 0.22/0.47    inference(resolution,[],[f116,f58])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X6,X10,X8,X7,X11,X9] : (~v1_relat_1(X11) | ~r2_hidden(k4_tarski(X6,X8),X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10))) | ~m1_subset_1(X9,k1_zfmisc_1(X11)) | r2_hidden(X6,X7)) )),
% 0.22/0.47    inference(resolution,[],[f114,f51])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X2) | r2_hidden(X0,X3) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.47    inference(resolution,[],[f113,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f112])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f73,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X6,X0,X5,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(X5,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(rectify,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~spl12_7 | ~spl12_8 | spl12_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f104,f77,f107,f101])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | spl12_1),
% 0.22/0.47    inference(superposition,[],[f78,f70])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1)) | spl12_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl12_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f45,f101])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & ((r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f28,f27,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ? [X4] : ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,X4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,X4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(X4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(X4,sK0)) => ((! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2)) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & (? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) & m1_subset_1(sK4,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ? [X6] : (r2_hidden(X6,sK1) & r2_hidden(k4_tarski(X6,sK4),sK3) & m1_subset_1(X6,sK2)) => (r2_hidden(sK5,sK1) & r2_hidden(k4_tarski(sK5,sK4),sK3) & m1_subset_1(sK5,sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(rectify,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : ((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(flattening,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : (((! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)))))),
% 0.22/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.47  fof(f11,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f10])).
% 0.22/0.47  fof(f10,conjecture,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl12_1 | spl12_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f89,f77])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    spl12_1 | spl12_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f85,f77])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    r2_hidden(sK5,sK1) | r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ~spl12_1 | spl12_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f80,f77])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(X5,sK4),sK3) | ~m1_subset_1(X5,sK2) | ~r2_hidden(sK4,k7_relset_1(sK2,sK0,sK3,sK1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (2857)------------------------------
% 0.22/0.47  % (2857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (2857)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (2857)Memory used [KB]: 11129
% 0.22/0.47  % (2857)Time elapsed: 0.079 s
% 0.22/0.47  % (2857)------------------------------
% 0.22/0.47  % (2857)------------------------------
% 0.22/0.47  % (2850)Success in time 0.111 s
%------------------------------------------------------------------------------

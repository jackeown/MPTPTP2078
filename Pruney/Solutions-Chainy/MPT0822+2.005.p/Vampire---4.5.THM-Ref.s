%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 196 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  343 ( 699 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f71,f75,f81,f86,f131,f134,f145,f150,f157,f166,f199,f201])).

fof(f201,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f199,plain,
    ( ~ spl9_3
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f198,f84,f57,f64])).

fof(f64,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f57,plain,
    ( spl9_1
  <=> ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f84,plain,
    ( spl9_7
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f198,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f195,f144])).

fof(f144,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f195,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f58,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f166,plain,
    ( ~ spl9_12
    | ~ spl9_5
    | spl9_16 ),
    inference(avatar_split_clause,[],[f165,f148,f73,f126])).

fof(f126,plain,
    ( spl9_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f73,plain,
    ( spl9_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f148,plain,
    ( spl9_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f165,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl9_5
    | spl9_16 ),
    inference(resolution,[],[f162,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_16 ),
    inference(resolution,[],[f149,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f149,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f157,plain,
    ( ~ spl9_5
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl9_5
    | spl9_15 ),
    inference(subsumption_resolution,[],[f74,f154])).

fof(f154,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl9_15 ),
    inference(resolution,[],[f143,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f143,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_15
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f150,plain,
    ( ~ spl9_16
    | ~ spl9_15
    | spl9_7
    | spl9_14 ),
    inference(avatar_split_clause,[],[f146,f139,f84,f142,f148])).

fof(f139,plain,
    ( spl9_14
  <=> r2_xboole_0(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f146,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | spl9_14 ),
    inference(resolution,[],[f140,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k2_relat_1(X0),X1)
      | k2_relat_1(X0) = X1
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f140,plain,
    ( ~ r2_xboole_0(k2_relat_1(sK2),sK1)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f145,plain,
    ( ~ spl9_14
    | ~ spl9_15
    | spl9_7
    | ~ spl9_4
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f137,f129,f68,f84,f142,f139])).

fof(f68,plain,
    ( spl9_4
  <=> ! [X5] :
        ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f129,plain,
    ( spl9_13
  <=> ! [X1,X0] :
        ( k2_relat_1(sK2) = X0
        | ~ v5_relat_1(sK2,X0)
        | ~ r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f137,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ r2_xboole_0(k2_relat_1(sK2),sK1)
    | ~ spl9_4
    | ~ spl9_13 ),
    inference(resolution,[],[f135,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK8(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(k2_relat_1(sK2),X0),sK1)
        | k2_relat_1(sK2) = X0
        | ~ v5_relat_1(sK2,X0) )
    | ~ spl9_4
    | ~ spl9_13 ),
    inference(resolution,[],[f130,f69])).

fof(f69,plain,
    ( ! [X5] :
        ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2)
        | ~ v5_relat_1(sK2,X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f134,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f127,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f131,plain,
    ( ~ spl9_12
    | spl9_13
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f124,f73,f129,f126])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(sK2) = X0
        | ~ r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2)
        | ~ v5_relat_1(sK2,X0)
        | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl9_5 ),
    inference(resolution,[],[f92,f74])).

fof(f92,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | k2_relat_1(X4) = X5
      | ~ r2_hidden(k4_tarski(X6,sK8(k2_relat_1(X4),X5)),X4)
      | ~ v5_relat_1(X4,X5)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f90,f41])).

fof(f90,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X2)
      | k2_relat_1(X1) = X2
      | ~ r2_hidden(k4_tarski(X3,sK8(k2_relat_1(X1),X2)),X1) ) ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(k2_relat_1(X0),X1),k2_relat_1(X0))
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,
    ( ~ spl9_7
    | spl9_2
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f82,f79,f60,f84])).

fof(f60,plain,
    ( spl9_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f79,plain,
    ( spl9_6
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f82,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl9_2
    | ~ spl9_6 ),
    inference(superposition,[],[f61,f80])).

fof(f80,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f61,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f81,plain,
    ( spl9_6
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f77,f73,f79])).

fof(f77,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl9_5 ),
    inference(resolution,[],[f52,f74])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f75,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X5] :
          ( r2_hidden(k4_tarski(sK4(X5),X5),sK2)
          | ~ r2_hidden(X5,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X5] :
              ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
              | ~ r2_hidden(X5,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
            | ~ r2_hidden(X5,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),sK2)
        & r2_hidden(X3,sK1) )
   => ( ! [X4] : ~ r2_hidden(k4_tarski(X4,sK3),sK2)
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5] :
      ( ? [X6] : r2_hidden(k4_tarski(X6,X5),sK2)
     => r2_hidden(k4_tarski(sK4(X5),X5),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X5] :
            ( ? [X6] : r2_hidden(k4_tarski(X6,X5),X2)
            | ~ r2_hidden(X5,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f71,plain,
    ( spl9_4
    | spl9_2 ),
    inference(avatar_split_clause,[],[f38,f60,f68])).

fof(f38,plain,(
    ! [X5] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | r2_hidden(k4_tarski(sK4(X5),X5),sK2)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f39,f60,f64])).

fof(f39,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f40,f60,f57])).

fof(f40,plain,(
    ! [X4] :
      ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(k4_tarski(X4,sK3),sK2) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30467)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (30475)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (30463)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (30458)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (30464)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (30468)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (30476)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (30464)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f62,f66,f71,f75,f81,f86,f131,f134,f145,f150,f157,f166,f199,f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~spl9_3 | ~spl9_1 | ~spl9_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f198,f84,f57,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl9_3 <=> r2_hidden(sK3,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl9_1 <=> ! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl9_7 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~r2_hidden(sK3,sK1) | (~spl9_1 | ~spl9_7)),
% 0.21/0.48    inference(forward_demodulation,[],[f195,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | ~spl9_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl9_1),
% 0.21/0.48    inference(resolution,[],[f58,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f30,f33,f32,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(X4,sK3),sK2)) ) | ~spl9_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ~spl9_12 | ~spl9_5 | spl9_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f148,f73,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl9_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl9_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl9_16 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl9_5 | spl9_16)),
% 0.21/0.48    inference(resolution,[],[f162,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_16),
% 0.21/0.48    inference(resolution,[],[f149,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl9_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ~spl9_5 | spl9_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    $false | (~spl9_5 | spl9_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl9_15),
% 0.21/0.48    inference(resolution,[],[f143,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ~v5_relat_1(sK2,sK1) | spl9_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl9_15 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~spl9_16 | ~spl9_15 | spl9_7 | spl9_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f146,f139,f84,f142,f148])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl9_14 <=> r2_xboole_0(k2_relat_1(sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | spl9_14),
% 0.21/0.48    inference(resolution,[],[f140,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_xboole_0(k2_relat_1(X0),X1) | k2_relat_1(X0) = X1 | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f45,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~r2_xboole_0(k2_relat_1(sK2),sK1) | spl9_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~spl9_14 | ~spl9_15 | spl9_7 | ~spl9_4 | ~spl9_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f137,f129,f68,f84,f142,f139])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl9_4 <=> ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl9_13 <=> ! [X1,X0] : (k2_relat_1(sK2) = X0 | ~v5_relat_1(sK2,X0) | ~r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~r2_xboole_0(k2_relat_1(sK2),sK1) | (~spl9_4 | ~spl9_13)),
% 0.21/0.48    inference(resolution,[],[f135,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK8(X0,X1),X0) & r2_hidden(sK8(X0,X1),X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(sK8(k2_relat_1(sK2),X0),sK1) | k2_relat_1(sK2) = X0 | ~v5_relat_1(sK2,X0)) ) | (~spl9_4 | ~spl9_13)),
% 0.21/0.48    inference(resolution,[],[f130,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) ) | ~spl9_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2) | ~v5_relat_1(sK2,X0) | k2_relat_1(sK2) = X0) ) | ~spl9_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl9_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    $false | spl9_12),
% 0.21/0.48    inference(resolution,[],[f127,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~spl9_12 | spl9_13 | ~spl9_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f73,f129,f126])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_relat_1(sK2) = X0 | ~r2_hidden(k4_tarski(X1,sK8(k2_relat_1(sK2),X0)),sK2) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))) ) | ~spl9_5),
% 0.21/0.48    inference(resolution,[],[f92,f74])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(X7)) | k2_relat_1(X4) = X5 | ~r2_hidden(k4_tarski(X6,sK8(k2_relat_1(X4),X5)),X4) | ~v5_relat_1(X4,X5) | ~v1_relat_1(X7)) )),
% 0.21/0.48    inference(resolution,[],[f90,f41])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X2) | k2_relat_1(X1) = X2 | ~r2_hidden(k4_tarski(X3,sK8(k2_relat_1(X1),X2)),X1)) )),
% 0.21/0.48    inference(resolution,[],[f87,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK8(k2_relat_1(X0),X1),k2_relat_1(X0)) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = X1) )),
% 0.21/0.48    inference(resolution,[],[f76,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_hidden(sK8(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl9_7 | spl9_2 | ~spl9_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f82,f79,f60,f84])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl9_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl9_6 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    sK1 != k2_relat_1(sK2) | (spl9_2 | ~spl9_6)),
% 0.21/0.48    inference(superposition,[],[f61,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl9_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | spl9_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl9_6 | ~spl9_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f77,f73,f79])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl9_5),
% 0.21/0.48    inference(resolution,[],[f52,f74])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl9_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f73])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    (sK1 != k2_relset_1(sK0,sK1,sK2) | (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f26,f25,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) | ~r2_hidden(X5,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),sK2) & r2_hidden(X3,sK1)) => (! [X4] : ~r2_hidden(k4_tarski(X4,sK3),sK2) & r2_hidden(sK3,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),sK2) => r2_hidden(k4_tarski(sK4(X5),X5),sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X5] : (? [X6] : r2_hidden(k4_tarski(X6,X5),X2) | ~r2_hidden(X5,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(rectify,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl9_4 | spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f60,f68])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X5] : (sK1 = k2_relset_1(sK0,sK1,sK2) | r2_hidden(k4_tarski(sK4(X5),X5),sK2) | ~r2_hidden(X5,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl9_3 | ~spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f60,f64])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl9_1 | ~spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f60,f57])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X4] : (sK1 != k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(k4_tarski(X4,sK3),sK2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30464)------------------------------
% 0.21/0.48  % (30464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30464)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30464)Memory used [KB]: 10746
% 0.21/0.48  % (30464)Time elapsed: 0.064 s
% 0.21/0.48  % (30464)------------------------------
% 0.21/0.48  % (30464)------------------------------
% 0.21/0.49  % (30462)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (30470)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30465)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (30457)Success in time 0.125 s
%------------------------------------------------------------------------------

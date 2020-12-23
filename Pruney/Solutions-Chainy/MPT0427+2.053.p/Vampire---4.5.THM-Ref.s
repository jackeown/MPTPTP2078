%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 231 expanded)
%              Number of leaves         :   36 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  329 ( 625 expanded)
%              Number of equality atoms :   59 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f619,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f83,f122,f179,f200,f221,f263,f431,f448,f504,f509,f565,f569,f570,f591,f618])).

fof(f618,plain,
    ( ~ spl5_2
    | spl5_7
    | spl5_38 ),
    inference(avatar_split_clause,[],[f614,f589,f139,f68])).

fof(f68,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f139,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f589,plain,
    ( spl5_38
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f614,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl5_38 ),
    inference(resolution,[],[f590,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f590,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f589])).

fof(f591,plain,
    ( ~ spl5_38
    | spl5_1
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f587,f567,f560,f64,f589])).

fof(f64,plain,
    ( spl5_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f560,plain,
    ( spl5_35
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f567,plain,
    ( spl5_37
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f587,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl5_1
    | ~ spl5_35
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f571,f568])).

fof(f568,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f567])).

fof(f571,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl5_1
    | ~ spl5_35 ),
    inference(superposition,[],[f65,f561])).

fof(f561,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f560])).

fof(f65,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f570,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f569,plain,
    ( spl5_37
    | spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f552,f76,f139,f567])).

fof(f76,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f552,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f267,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f267,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f565,plain,
    ( spl5_35
    | spl5_36
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f551,f72,f563,f560])).

fof(f563,plain,
    ( spl5_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f72,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f551,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f267,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f509,plain,
    ( spl5_7
    | ~ spl5_29
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f505,f502,f507,f139])).

fof(f507,plain,
    ( spl5_29
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f502,plain,
    ( spl5_28
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(sK3(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f505,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl5_28 ),
    inference(resolution,[],[f503,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f503,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1),X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f502])).

fof(f504,plain,
    ( spl5_7
    | spl5_28
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f498,f446,f502,f139])).

fof(f446,plain,
    ( spl5_24
  <=> sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(sK3(sK1),X0)
        | k1_xboole_0 = sK1 )
    | ~ spl5_24 ),
    inference(resolution,[],[f485,f45])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r1_tarski(X0,k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_24 ),
    inference(resolution,[],[f476,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f476,plain,
    ( ! [X3] :
        ( r1_xboole_0(X3,sK1)
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl5_24 ),
    inference(superposition,[],[f59,f447])).

fof(f447,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f446])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f448,plain,
    ( spl5_24
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f432,f429,f120,f446])).

fof(f120,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f429,plain,
    ( spl5_23
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f432,plain,
    ( sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_23 ),
    inference(superposition,[],[f124,f430])).

fof(f430,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f429])).

fof(f124,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,sK1))
    | ~ spl5_6 ),
    inference(resolution,[],[f121,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    inference(resolution,[],[f59,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f121,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f431,plain,
    ( spl5_23
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f424,f68,f429])).

fof(f424,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f281,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f281,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k4_xboole_0(X4,sK2)))
        | k4_xboole_0(X3,sK1) = X3 )
    | ~ spl5_2 ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f134,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X3,k4_xboole_0(X4,sK2))
        | k4_xboole_0(X3,sK1) = X3 )
    | ~ spl5_2 ),
    inference(resolution,[],[f115,f55])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,sK1)
        | ~ r1_tarski(X1,k4_xboole_0(X0,sK2)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f59,f111])).

fof(f111,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f69])).

fof(f69,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f263,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | spl5_12 ),
    inference(avatar_split_clause,[],[f261,f177,f204,f194])).

fof(f194,plain,
    ( spl5_14
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f204,plain,
    ( spl5_16
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f177,plain,
    ( spl5_12
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f261,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl5_12 ),
    inference(superposition,[],[f178,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f178,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f221,plain,
    ( spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f216,f72,f204])).

fof(f216,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f200,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f179,plain,
    ( ~ spl5_12
    | spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f157,f139,f81,f177])).

fof(f81,plain,
    ( spl5_5
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f157,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f82,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f82,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f122,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f117,f68,f120])).

fof(f117,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f46,f111])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f83,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f79,f64,f81])).

fof(f79,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl5_1 ),
    inference(resolution,[],[f57,f65])).

fof(f78,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f68])).

fof(f42,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f43,f64])).

fof(f43,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:02:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.46  % (2975)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (2967)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (2965)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (2963)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (2973)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (2971)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (2970)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (2978)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (2976)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (2977)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (2980)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (2974)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (2966)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (2964)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (2960)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (2969)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (2979)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (2961)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (2962)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (2972)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (2968)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (2966)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f619,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f83,f122,f179,f200,f221,f263,f431,f448,f504,f509,f565,f569,f570,f591,f618])).
% 0.20/0.52  fof(f618,plain,(
% 0.20/0.52    ~spl5_2 | spl5_7 | spl5_38),
% 0.20/0.52    inference(avatar_split_clause,[],[f614,f589,f139,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl5_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    spl5_7 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.52  fof(f589,plain,(
% 0.20/0.52    spl5_38 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.52  fof(f614,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl5_38),
% 0.20/0.52    inference(resolution,[],[f590,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.20/0.52  fof(f590,plain,(
% 0.20/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl5_38),
% 0.20/0.52    inference(avatar_component_clause,[],[f589])).
% 0.20/0.52  fof(f591,plain,(
% 0.20/0.52    ~spl5_38 | spl5_1 | ~spl5_35 | ~spl5_37),
% 0.20/0.52    inference(avatar_split_clause,[],[f587,f567,f560,f64,f589])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl5_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f560,plain,(
% 0.20/0.52    spl5_35 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.20/0.52  fof(f567,plain,(
% 0.20/0.52    spl5_37 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.52  fof(f587,plain,(
% 0.20/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl5_1 | ~spl5_35 | ~spl5_37)),
% 0.20/0.52    inference(forward_demodulation,[],[f571,f568])).
% 0.20/0.52  fof(f568,plain,(
% 0.20/0.52    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl5_37),
% 0.20/0.52    inference(avatar_component_clause,[],[f567])).
% 0.20/0.52  fof(f571,plain,(
% 0.20/0.52    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl5_1 | ~spl5_35)),
% 0.20/0.52    inference(superposition,[],[f65,f561])).
% 0.20/0.52  fof(f561,plain,(
% 0.20/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl5_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f560])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f570,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(sK1,sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f569,plain,(
% 0.20/0.52    spl5_37 | spl5_7 | ~spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f552,f76,f139,f567])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl5_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.52  fof(f552,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl5_4),
% 0.20/0.52    inference(resolution,[],[f267,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f76])).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f264])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.20/0.52    inference(superposition,[],[f53,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.20/0.52  fof(f565,plain,(
% 0.20/0.52    spl5_35 | spl5_36 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f551,f72,f563,f560])).
% 0.20/0.52  fof(f563,plain,(
% 0.20/0.52    spl5_36 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f551,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl5_3),
% 0.20/0.52    inference(resolution,[],[f267,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f72])).
% 0.20/0.52  fof(f509,plain,(
% 0.20/0.52    spl5_7 | ~spl5_29 | ~spl5_28),
% 0.20/0.52    inference(avatar_split_clause,[],[f505,f502,f507,f139])).
% 0.20/0.52  fof(f507,plain,(
% 0.20/0.52    spl5_29 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.52  fof(f502,plain,(
% 0.20/0.52    spl5_28 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(sK3(sK1),X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.52  fof(f505,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 | ~spl5_28),
% 0.20/0.52    inference(resolution,[],[f503,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f503,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK3(sK1),X0) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl5_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f502])).
% 0.20/0.52  fof(f504,plain,(
% 0.20/0.52    spl5_7 | spl5_28 | ~spl5_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f498,f446,f502,f139])).
% 0.20/0.52  fof(f446,plain,(
% 0.20/0.52    spl5_24 <=> sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.52  fof(f498,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(sK3(sK1),X0) | k1_xboole_0 = sK1) ) | ~spl5_24),
% 0.20/0.52    inference(resolution,[],[f485,f45])).
% 0.20/0.52  fof(f485,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X0)) ) | ~spl5_24),
% 0.20/0.52    inference(resolution,[],[f476,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.52  fof(f476,plain,(
% 0.20/0.52    ( ! [X3] : (r1_xboole_0(X3,sK1) | ~r1_tarski(X3,k1_xboole_0)) ) | ~spl5_24),
% 0.20/0.52    inference(superposition,[],[f59,f447])).
% 0.20/0.52  fof(f447,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK1,k1_xboole_0) | ~spl5_24),
% 0.20/0.52    inference(avatar_component_clause,[],[f446])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.52  fof(f448,plain,(
% 0.20/0.52    spl5_24 | ~spl5_6 | ~spl5_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f432,f429,f120,f446])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl5_6 <=> r1_tarski(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.52  fof(f429,plain,(
% 0.20/0.52    spl5_23 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK1,k1_xboole_0) | (~spl5_6 | ~spl5_23)),
% 0.20/0.52    inference(superposition,[],[f124,f430])).
% 0.20/0.52  fof(f430,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl5_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f429])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) ) | ~spl5_6),
% 0.20/0.52    inference(resolution,[],[f121,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) )),
% 0.20/0.52    inference(resolution,[],[f59,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    r1_tarski(sK1,sK1) | ~spl5_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f120])).
% 0.20/0.52  fof(f431,plain,(
% 0.20/0.52    spl5_23 | ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f424,f68,f429])).
% 0.20/0.52  fof(f424,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | ~spl5_2),
% 0.20/0.52    inference(resolution,[],[f281,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k4_xboole_0(X4,sK2))) | k4_xboole_0(X3,sK1) = X3) ) | ~spl5_2),
% 0.20/0.52    inference(resolution,[],[f134,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r1_tarski(X3,k4_xboole_0(X4,sK2)) | k4_xboole_0(X3,sK1) = X3) ) | ~spl5_2),
% 0.20/0.52    inference(resolution,[],[f115,f55])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,sK1) | ~r1_tarski(X1,k4_xboole_0(X0,sK2))) ) | ~spl5_2),
% 0.20/0.52    inference(superposition,[],[f59,f111])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | ~spl5_2),
% 0.20/0.52    inference(resolution,[],[f85,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2) | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    ~spl5_14 | ~spl5_16 | spl5_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f261,f177,f204,f194])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    spl5_14 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    spl5_16 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl5_12 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl5_12),
% 0.20/0.52    inference(superposition,[],[f178,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | spl5_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f177])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    spl5_16 | ~spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f216,f72,f204])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl5_3),
% 0.20/0.52    inference(resolution,[],[f52,f73])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ~spl5_12 | spl5_5 | ~spl5_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f157,f139,f81,f177])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl5_5 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl5_5 | ~spl5_7)),
% 0.20/0.52    inference(superposition,[],[f82,f140])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl5_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f139])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl5_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl5_6 | ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f117,f68,f120])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    r1_tarski(sK1,sK1) | ~spl5_2),
% 0.20/0.52    inference(superposition,[],[f46,f111])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ~spl5_5 | spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f79,f64,f81])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl5_1),
% 0.20/0.52    inference(resolution,[],[f57,f65])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    spl5_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f76])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f32,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f14])).
% 0.20/0.52  fof(f14,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl5_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f72])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f68])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f43,f64])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (2966)------------------------------
% 0.20/0.52  % (2966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2966)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (2966)Memory used [KB]: 11001
% 0.20/0.52  % (2966)Time elapsed: 0.102 s
% 0.20/0.52  % (2966)------------------------------
% 0.20/0.52  % (2966)------------------------------
% 0.20/0.52  % (2959)Success in time 0.175 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:06:43 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 291 expanded)
%              Number of leaves         :   36 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  447 (1328 expanded)
%              Number of equality atoms :   62 ( 236 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f125,f130,f135,f140,f145,f150,f155,f187,f222,f286,f384,f385,f395,f396,f418,f429,f464,f495,f705,f734,f735])).

fof(f735,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f734,plain,
    ( spl7_56
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f726,f491,f216,f113,f730])).

fof(f730,plain,
    ( spl7_56
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f113,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f216,plain,
    ( spl7_14
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f491,plain,
    ( spl7_46
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f726,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_46 ),
    inference(resolution,[],[f654,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f654,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f493,f646,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f646,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f399,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f399,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f217,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f217,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f493,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f491])).

fof(f705,plain,
    ( spl7_54
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f697,f460,f216,f113,f701])).

fof(f701,plain,
    ( spl7_54
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f460,plain,
    ( spl7_43
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f697,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(resolution,[],[f653,f73])).

fof(f653,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_43 ),
    inference(unit_resulting_resolution,[],[f462,f646,f79])).

fof(f462,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f460])).

fof(f495,plain,
    ( spl7_46
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f479,f426,f491])).

fof(f426,plain,
    ( spl7_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f479,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_39 ),
    inference(resolution,[],[f428,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f428,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f426])).

fof(f464,plain,
    ( spl7_43
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f448,f415,f460])).

fof(f415,plain,
    ( spl7_37
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f448,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_37 ),
    inference(resolution,[],[f417,f82])).

fof(f417,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f415])).

fof(f429,plain,
    ( spl7_39
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f424,f142,f113,f426])).

% (3470)Termination reason: Refutation not found, incomplete strategy

% (3470)Memory used [KB]: 11001
% (3470)Time elapsed: 0.158 s
% (3470)------------------------------
% (3470)------------------------------
fof(f142,plain,
    ( spl7_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f424,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f404,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f144,f114])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f418,plain,
    ( spl7_37
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f413,f127,f113,f415])).

fof(f127,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f413,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f402,f99])).

fof(f402,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f129,f114])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f396,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f395,plain,
    ( spl7_35
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f388,f332,f267,f152,f142,f137,f127,f122,f392])).

fof(f392,plain,
    ( spl7_35
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f122,plain,
    ( spl7_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f137,plain,
    ( spl7_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f152,plain,
    ( spl7_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f267,plain,
    ( spl7_20
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f332,plain,
    ( spl7_28
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f388,plain,
    ( sK2 = sK3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f154,f139,f124,f269,f129,f144,f334,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f334,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f332])).

fof(f269,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f267])).

fof(f124,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f139,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f154,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f385,plain,
    ( spl7_20
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_14 ),
    inference(avatar_split_clause,[],[f381,f216,f137,f132,f127,f267])).

fof(f132,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f381,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f139,f134,f129,f218,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f218,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f134,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f384,plain,
    ( spl7_28
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14 ),
    inference(avatar_split_clause,[],[f382,f216,f152,f147,f142,f332])).

fof(f147,plain,
    ( spl7_9
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f382,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f154,f149,f144,f218,f78])).

fof(f149,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f286,plain,
    ( spl7_16
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f236,f127,f245])).

fof(f245,plain,
    ( spl7_16
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f236,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f129,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f222,plain,
    ( ~ spl7_14
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f214,f184,f216])).

fof(f184,plain,
    ( spl7_13
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f214,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_13 ),
    inference(resolution,[],[f186,f72])).

fof(f186,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( spl7_13
    | spl7_2 ),
    inference(avatar_split_clause,[],[f166,f113,f184])).

fof(f166,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f115,f73])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f155,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f58,f152])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f150,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f59,f147])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f145,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f60,f142])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f61,f137])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f62,f132])).

fof(f62,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f63,f127])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f64,f122])).

fof(f64,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f66,f108])).

fof(f108,plain,
    ( spl7_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f66,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (3468)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (3483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (3472)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (3476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (3468)Refutation not found, incomplete strategy% (3468)------------------------------
% 0.20/0.50  % (3468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3468)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3468)Memory used [KB]: 1663
% 0.20/0.50  % (3468)Time elapsed: 0.103 s
% 0.20/0.50  % (3468)------------------------------
% 0.20/0.50  % (3468)------------------------------
% 0.20/0.51  % (3484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (3482)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (3475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (3469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (3474)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (3491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.52  % (3470)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.53  % (3471)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (3473)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.53  % (3492)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.53  % (3477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.53  % (3490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.53  % (3496)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.53  % (3476)Refutation not found, incomplete strategy% (3476)------------------------------
% 1.35/0.53  % (3476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (3476)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (3476)Memory used [KB]: 10874
% 1.35/0.53  % (3476)Time elapsed: 0.136 s
% 1.35/0.53  % (3476)------------------------------
% 1.35/0.53  % (3476)------------------------------
% 1.35/0.53  % (3493)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (3494)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (3497)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (3495)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (3480)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (3486)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (3487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.54  % (3489)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.54  % (3478)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.54  % (3481)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.54  % (3489)Refutation not found, incomplete strategy% (3489)------------------------------
% 1.47/0.54  % (3489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (3485)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.55  % (3488)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (3485)Refutation not found, incomplete strategy% (3485)------------------------------
% 1.47/0.55  % (3485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (3485)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (3485)Memory used [KB]: 10618
% 1.47/0.55  % (3485)Time elapsed: 0.149 s
% 1.47/0.55  % (3485)------------------------------
% 1.47/0.55  % (3485)------------------------------
% 1.47/0.55  % (3479)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (3489)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (3489)Memory used [KB]: 1791
% 1.47/0.55  % (3489)Time elapsed: 0.153 s
% 1.47/0.55  % (3489)------------------------------
% 1.47/0.55  % (3489)------------------------------
% 1.47/0.56  % (3493)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % (3470)Refutation not found, incomplete strategy% (3470)------------------------------
% 1.47/0.56  % (3470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f737,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f111,f125,f130,f135,f140,f145,f150,f155,f187,f222,f286,f384,f385,f395,f396,f418,f429,f464,f495,f705,f734,f735])).
% 1.47/0.56  fof(f735,plain,(
% 1.47/0.56    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 1.47/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.47/0.56  fof(f734,plain,(
% 1.47/0.56    spl7_56 | ~spl7_2 | ~spl7_14 | ~spl7_46),
% 1.47/0.56    inference(avatar_split_clause,[],[f726,f491,f216,f113,f730])).
% 1.47/0.56  fof(f730,plain,(
% 1.47/0.56    spl7_56 <=> k1_xboole_0 = sK2),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 1.47/0.56  fof(f113,plain,(
% 1.47/0.56    spl7_2 <=> k1_xboole_0 = sK1),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.47/0.56  fof(f216,plain,(
% 1.47/0.56    spl7_14 <=> v1_xboole_0(sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.47/0.56  fof(f491,plain,(
% 1.47/0.56    spl7_46 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.47/0.56  fof(f726,plain,(
% 1.47/0.56    k1_xboole_0 = sK2 | (~spl7_2 | ~spl7_14 | ~spl7_46)),
% 1.47/0.56    inference(resolution,[],[f654,f73])).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f47])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.47/0.56    inference(ennf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.47/0.56  fof(f654,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl7_2 | ~spl7_14 | ~spl7_46)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f493,f646,f79])).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.56  fof(f646,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl7_2 | ~spl7_14)),
% 1.47/0.56    inference(forward_demodulation,[],[f399,f114])).
% 1.47/0.56  fof(f114,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | ~spl7_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f113])).
% 1.47/0.56  fof(f399,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl7_14),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f217,f72])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f20])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.56  fof(f217,plain,(
% 1.47/0.56    v1_xboole_0(sK1) | ~spl7_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f216])).
% 1.47/0.56  fof(f493,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl7_46),
% 1.47/0.56    inference(avatar_component_clause,[],[f491])).
% 1.47/0.56  fof(f705,plain,(
% 1.47/0.56    spl7_54 | ~spl7_2 | ~spl7_14 | ~spl7_43),
% 1.47/0.56    inference(avatar_split_clause,[],[f697,f460,f216,f113,f701])).
% 1.47/0.56  fof(f701,plain,(
% 1.47/0.56    spl7_54 <=> k1_xboole_0 = sK3),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 1.47/0.56  fof(f460,plain,(
% 1.47/0.56    spl7_43 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 1.47/0.56  fof(f697,plain,(
% 1.47/0.56    k1_xboole_0 = sK3 | (~spl7_2 | ~spl7_14 | ~spl7_43)),
% 1.47/0.56    inference(resolution,[],[f653,f73])).
% 1.47/0.56  fof(f653,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | (~spl7_2 | ~spl7_14 | ~spl7_43)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f462,f646,f79])).
% 1.47/0.56  fof(f462,plain,(
% 1.47/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl7_43),
% 1.47/0.56    inference(avatar_component_clause,[],[f460])).
% 1.47/0.56  fof(f495,plain,(
% 1.47/0.56    spl7_46 | ~spl7_39),
% 1.47/0.56    inference(avatar_split_clause,[],[f479,f426,f491])).
% 1.47/0.56  fof(f426,plain,(
% 1.47/0.56    spl7_39 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.47/0.56  fof(f479,plain,(
% 1.47/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl7_39),
% 1.47/0.56    inference(resolution,[],[f428,f82])).
% 1.47/0.56  fof(f82,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f54])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.56    inference(nnf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.56  fof(f428,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_39),
% 1.47/0.56    inference(avatar_component_clause,[],[f426])).
% 1.47/0.56  fof(f464,plain,(
% 1.47/0.56    spl7_43 | ~spl7_37),
% 1.47/0.56    inference(avatar_split_clause,[],[f448,f415,f460])).
% 1.47/0.56  fof(f415,plain,(
% 1.47/0.56    spl7_37 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.47/0.56  fof(f448,plain,(
% 1.47/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl7_37),
% 1.47/0.56    inference(resolution,[],[f417,f82])).
% 1.47/0.56  fof(f417,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_37),
% 1.47/0.56    inference(avatar_component_clause,[],[f415])).
% 1.47/0.56  fof(f429,plain,(
% 1.47/0.56    spl7_39 | ~spl7_2 | ~spl7_8),
% 1.47/0.56    inference(avatar_split_clause,[],[f424,f142,f113,f426])).
% 1.47/0.56  % (3470)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (3470)Memory used [KB]: 11001
% 1.47/0.56  % (3470)Time elapsed: 0.158 s
% 1.47/0.56  % (3470)------------------------------
% 1.47/0.56  % (3470)------------------------------
% 1.47/0.56  fof(f142,plain,(
% 1.47/0.56    spl7_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.47/0.56  fof(f424,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_8)),
% 1.47/0.56    inference(forward_demodulation,[],[f404,f99])).
% 1.47/0.56  fof(f99,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.47/0.56    inference(equality_resolution,[],[f86])).
% 1.47/0.56  fof(f86,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.56    inference(flattening,[],[f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.47/0.56  fof(f404,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_8)),
% 1.47/0.56    inference(backward_demodulation,[],[f144,f114])).
% 1.47/0.56  fof(f144,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_8),
% 1.47/0.56    inference(avatar_component_clause,[],[f142])).
% 1.47/0.56  fof(f418,plain,(
% 1.47/0.56    spl7_37 | ~spl7_2 | ~spl7_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f413,f127,f113,f415])).
% 1.47/0.56  fof(f127,plain,(
% 1.47/0.56    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.47/0.56  fof(f413,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_2 | ~spl7_5)),
% 1.47/0.56    inference(forward_demodulation,[],[f402,f99])).
% 1.47/0.56  fof(f402,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_2 | ~spl7_5)),
% 1.47/0.56    inference(backward_demodulation,[],[f129,f114])).
% 1.47/0.56  fof(f129,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f127])).
% 1.47/0.56  fof(f396,plain,(
% 1.47/0.56    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.47/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.47/0.56  fof(f395,plain,(
% 1.47/0.56    spl7_35 | ~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_20 | ~spl7_28),
% 1.47/0.56    inference(avatar_split_clause,[],[f388,f332,f267,f152,f142,f137,f127,f122,f392])).
% 1.47/0.56  fof(f392,plain,(
% 1.47/0.56    spl7_35 <=> sK2 = sK3),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.47/0.56  fof(f122,plain,(
% 1.47/0.56    spl7_4 <=> r1_partfun1(sK2,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.47/0.56  fof(f137,plain,(
% 1.47/0.56    spl7_7 <=> v1_funct_1(sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.47/0.56  fof(f152,plain,(
% 1.47/0.56    spl7_10 <=> v1_funct_1(sK2)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.47/0.56  fof(f267,plain,(
% 1.47/0.56    spl7_20 <=> v1_partfun1(sK3,sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.47/0.56  fof(f332,plain,(
% 1.47/0.56    spl7_28 <=> v1_partfun1(sK2,sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.47/0.56  fof(f388,plain,(
% 1.47/0.56    sK2 = sK3 | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_20 | ~spl7_28)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f154,f139,f124,f269,f129,f144,f334,f95])).
% 1.47/0.56  fof(f95,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f36])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.47/0.56  fof(f334,plain,(
% 1.47/0.56    v1_partfun1(sK2,sK0) | ~spl7_28),
% 1.47/0.56    inference(avatar_component_clause,[],[f332])).
% 1.47/0.56  fof(f269,plain,(
% 1.47/0.56    v1_partfun1(sK3,sK0) | ~spl7_20),
% 1.47/0.56    inference(avatar_component_clause,[],[f267])).
% 1.47/0.56  fof(f124,plain,(
% 1.47/0.56    r1_partfun1(sK2,sK3) | ~spl7_4),
% 1.47/0.56    inference(avatar_component_clause,[],[f122])).
% 1.47/0.56  fof(f139,plain,(
% 1.47/0.56    v1_funct_1(sK3) | ~spl7_7),
% 1.47/0.56    inference(avatar_component_clause,[],[f137])).
% 1.47/0.56  fof(f154,plain,(
% 1.47/0.56    v1_funct_1(sK2) | ~spl7_10),
% 1.47/0.56    inference(avatar_component_clause,[],[f152])).
% 1.47/0.56  fof(f385,plain,(
% 1.47/0.56    spl7_20 | ~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_14),
% 1.47/0.56    inference(avatar_split_clause,[],[f381,f216,f137,f132,f127,f267])).
% 1.47/0.56  fof(f132,plain,(
% 1.47/0.56    spl7_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.47/0.56  fof(f381,plain,(
% 1.47/0.56    v1_partfun1(sK3,sK0) | (~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_14)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f139,f134,f129,f218,f78])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.56    inference(flattening,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,axiom,(
% 1.47/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.47/0.56  fof(f218,plain,(
% 1.47/0.56    ~v1_xboole_0(sK1) | spl7_14),
% 1.47/0.56    inference(avatar_component_clause,[],[f216])).
% 1.47/0.56  fof(f134,plain,(
% 1.47/0.56    v1_funct_2(sK3,sK0,sK1) | ~spl7_6),
% 1.47/0.56    inference(avatar_component_clause,[],[f132])).
% 1.47/0.56  fof(f384,plain,(
% 1.47/0.56    spl7_28 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_14),
% 1.47/0.56    inference(avatar_split_clause,[],[f382,f216,f152,f147,f142,f332])).
% 1.47/0.56  fof(f147,plain,(
% 1.47/0.56    spl7_9 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.47/0.56  fof(f382,plain,(
% 1.47/0.56    v1_partfun1(sK2,sK0) | (~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_14)),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f154,f149,f144,f218,f78])).
% 1.47/0.56  fof(f149,plain,(
% 1.47/0.56    v1_funct_2(sK2,sK0,sK1) | ~spl7_9),
% 1.47/0.56    inference(avatar_component_clause,[],[f147])).
% 1.47/0.56  fof(f286,plain,(
% 1.47/0.56    spl7_16 | ~spl7_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f236,f127,f245])).
% 1.47/0.56  fof(f245,plain,(
% 1.47/0.56    spl7_16 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.47/0.56  fof(f236,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl7_5),
% 1.47/0.56    inference(resolution,[],[f129,f106])).
% 1.47/0.56  fof(f106,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 1.47/0.56    inference(condensation,[],[f98])).
% 1.47/0.56  fof(f98,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.56    inference(flattening,[],[f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.47/0.56    inference(ennf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.47/0.56  fof(f222,plain,(
% 1.47/0.56    ~spl7_14 | ~spl7_13),
% 1.47/0.56    inference(avatar_split_clause,[],[f214,f184,f216])).
% 1.47/0.56  fof(f184,plain,(
% 1.47/0.56    spl7_13 <=> r2_hidden(sK4(sK1),sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.47/0.56  fof(f214,plain,(
% 1.47/0.56    ~v1_xboole_0(sK1) | ~spl7_13),
% 1.47/0.56    inference(resolution,[],[f186,f72])).
% 1.47/0.56  fof(f186,plain,(
% 1.47/0.56    r2_hidden(sK4(sK1),sK1) | ~spl7_13),
% 1.47/0.56    inference(avatar_component_clause,[],[f184])).
% 1.47/0.56  fof(f187,plain,(
% 1.47/0.56    spl7_13 | spl7_2),
% 1.47/0.56    inference(avatar_split_clause,[],[f166,f113,f184])).
% 1.47/0.56  fof(f166,plain,(
% 1.47/0.56    r2_hidden(sK4(sK1),sK1) | spl7_2),
% 1.47/0.56    inference(unit_resulting_resolution,[],[f115,f73])).
% 1.47/0.56  fof(f115,plain,(
% 1.47/0.56    k1_xboole_0 != sK1 | spl7_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f113])).
% 1.47/0.56  fof(f155,plain,(
% 1.47/0.56    spl7_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f58,f152])).
% 1.47/0.56  fof(f58,plain,(
% 1.47/0.56    v1_funct_1(sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f44,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.47/0.56    inference(negated_conjecture,[],[f18])).
% 1.47/0.56  fof(f18,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 1.47/0.56  fof(f150,plain,(
% 1.47/0.56    spl7_9),
% 1.47/0.56    inference(avatar_split_clause,[],[f59,f147])).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f145,plain,(
% 1.47/0.56    spl7_8),
% 1.47/0.56    inference(avatar_split_clause,[],[f60,f142])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f140,plain,(
% 1.47/0.56    spl7_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f61,f137])).
% 1.47/0.56  fof(f61,plain,(
% 1.47/0.56    v1_funct_1(sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f135,plain,(
% 1.47/0.56    spl7_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f62,f132])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f130,plain,(
% 1.47/0.56    spl7_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f63,f127])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f125,plain,(
% 1.47/0.56    spl7_4),
% 1.47/0.56    inference(avatar_split_clause,[],[f64,f122])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    r1_partfun1(sK2,sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  fof(f111,plain,(
% 1.47/0.56    ~spl7_1),
% 1.47/0.56    inference(avatar_split_clause,[],[f66,f108])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    spl7_1 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f45])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (3493)------------------------------
% 1.47/0.56  % (3493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3493)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (3493)Memory used [KB]: 6524
% 1.47/0.56  % (3493)Time elapsed: 0.146 s
% 1.47/0.56  % (3493)------------------------------
% 1.47/0.56  % (3493)------------------------------
% 1.47/0.57  % (3467)Success in time 0.208 s
%------------------------------------------------------------------------------

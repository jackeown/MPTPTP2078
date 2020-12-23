%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0381+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 150 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1322,f1327,f1539,f1622,f1651])).

fof(f1651,plain,
    ( ~ spl35_23
    | spl35_1 ),
    inference(avatar_split_clause,[],[f1647,f1319,f1619])).

fof(f1619,plain,
    ( spl35_23
  <=> r2_hidden(k1_tarski(sK2),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_23])])).

fof(f1319,plain,
    ( spl35_1
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_1])])).

fof(f1647,plain,
    ( ~ r2_hidden(k1_tarski(sK2),k1_zfmisc_1(sK3))
    | spl35_1 ),
    inference(unit_resulting_resolution,[],[f890,f1321,f866])).

fof(f866,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f708])).

fof(f708,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f590])).

fof(f590,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1321,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK3))
    | spl35_1 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f890,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f476,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f1622,plain,
    ( spl35_23
    | ~ spl35_17 ),
    inference(avatar_split_clause,[],[f1616,f1536,f1619])).

fof(f1536,plain,
    ( spl35_17
  <=> r1_tarski(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_17])])).

fof(f1616,plain,
    ( r2_hidden(k1_tarski(sK2),k1_zfmisc_1(sK3))
    | ~ spl35_17 ),
    inference(unit_resulting_resolution,[],[f1538,f1245])).

fof(f1245,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f877])).

fof(f877,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f718])).

fof(f718,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK15(X0,X1),X0)
            | ~ r2_hidden(sK15(X0,X1),X1) )
          & ( r1_tarski(sK15(X0,X1),X0)
            | r2_hidden(sK15(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f716,f717])).

fof(f717,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK15(X0,X1),X0)
          | ~ r2_hidden(sK15(X0,X1),X1) )
        & ( r1_tarski(sK15(X0,X1),X0)
          | r2_hidden(sK15(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f716,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f715])).

fof(f715,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1538,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl35_17 ),
    inference(avatar_component_clause,[],[f1536])).

fof(f1539,plain,
    ( spl35_17
    | ~ spl35_2 ),
    inference(avatar_split_clause,[],[f1532,f1324,f1536])).

fof(f1324,plain,
    ( spl35_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_2])])).

fof(f1532,plain,
    ( r1_tarski(k1_tarski(sK2),sK3)
    | ~ spl35_2 ),
    inference(unit_resulting_resolution,[],[f1326,f984])).

fof(f984,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f1326,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl35_2 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f1327,plain,(
    spl35_2 ),
    inference(avatar_split_clause,[],[f819,f1324])).

fof(f819,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f680])).

fof(f680,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK3))
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f540,f679])).

fof(f679,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK3))
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f540,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f534])).

fof(f534,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f1322,plain,(
    ~ spl35_1 ),
    inference(avatar_split_clause,[],[f820,f1319])).

fof(f820,plain,(
    ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f680])).
%------------------------------------------------------------------------------

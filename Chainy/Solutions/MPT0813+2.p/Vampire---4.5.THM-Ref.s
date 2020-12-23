%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0813+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 147 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1511,f1515,f1519,f1595,f1607,f1668])).

fof(f1668,plain,
    ( ~ spl31_2
    | ~ spl31_15
    | spl31_17 ),
    inference(avatar_contradiction_clause,[],[f1661])).

fof(f1661,plain,
    ( $false
    | ~ spl31_2
    | ~ spl31_15
    | spl31_17 ),
    inference(unit_resulting_resolution,[],[f1514,f1594,f1606,f1353])).

fof(f1353,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1217])).

fof(f1217,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1216])).

fof(f1216,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1606,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | spl31_17 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f1605,plain,
    ( spl31_17
  <=> r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_17])])).

fof(f1594,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl31_15 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f1593,plain,
    ( spl31_15
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_15])])).

fof(f1514,plain,
    ( r1_tarski(sK0,sK3)
    | ~ spl31_2 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f1513,plain,
    ( spl31_2
  <=> r1_tarski(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_2])])).

% (719)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f1607,plain,
    ( ~ spl31_17
    | spl31_1 ),
    inference(avatar_split_clause,[],[f1601,f1509,f1605])).

fof(f1509,plain,
    ( spl31_1
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1])])).

fof(f1601,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | spl31_1 ),
    inference(resolution,[],[f1365,f1510])).

fof(f1510,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl31_1 ),
    inference(avatar_component_clause,[],[f1509])).

fof(f1365,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f1294,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1595,plain,
    ( spl31_15
    | ~ spl31_3 ),
    inference(avatar_split_clause,[],[f1589,f1517,f1593])).

fof(f1517,plain,
    ( spl31_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_3])])).

fof(f1589,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ spl31_3 ),
    inference(resolution,[],[f1364,f1518])).

fof(f1518,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl31_3 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1364,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1294])).

fof(f1519,plain,(
    spl31_3 ),
    inference(avatar_split_clause,[],[f1350,f1517])).

fof(f1350,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f1285])).

fof(f1285,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1215,f1284])).

fof(f1284,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f1215,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f1214])).

fof(f1214,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(X0,X3)
         => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f1212])).

fof(f1212,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

fof(f1515,plain,(
    spl31_2 ),
    inference(avatar_split_clause,[],[f1351,f1513])).

fof(f1351,plain,(
    r1_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f1285])).

fof(f1511,plain,(
    ~ spl31_1 ),
    inference(avatar_split_clause,[],[f1352,f1509])).

fof(f1352,plain,(
    ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f1285])).
%------------------------------------------------------------------------------

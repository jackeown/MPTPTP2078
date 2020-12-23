%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0358+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 154 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 ( 376 expanded)
%              Number of equality atoms :   49 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1845,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1327,f1341,f1346,f1437,f1547,f1775,f1821])).

fof(f1821,plain,
    ( ~ spl31_1
    | spl31_8
    | ~ spl31_9
    | ~ spl31_14 ),
    inference(avatar_contradiction_clause,[],[f1820])).

fof(f1820,plain,
    ( $false
    | ~ spl31_1
    | spl31_8
    | ~ spl31_9
    | ~ spl31_14 ),
    inference(subsumption_resolution,[],[f1819,f1750])).

fof(f1750,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl31_1
    | spl31_8 ),
    inference(forward_demodulation,[],[f1749,f1301])).

fof(f1301,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f1296,f884])).

fof(f884,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f1296,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f834,f836])).

fof(f836,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f834,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f490])).

fof(f490,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f1749,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k1_xboole_0),k4_xboole_0(sK0,sK1))
    | ~ spl31_1
    | spl31_8 ),
    inference(forward_demodulation,[],[f1743,f1525])).

fof(f1525,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl31_1 ),
    inference(unit_resulting_resolution,[],[f1326,f857])).

fof(f857,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f527])).

% (16462)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f527,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1326,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl31_1 ),
    inference(avatar_component_clause,[],[f1324])).

fof(f1324,plain,
    ( spl31_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1])])).

fof(f1743,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k1_xboole_0),k3_subset_1(sK0,sK1))
    | ~ spl31_1
    | spl31_8 ),
    inference(unit_resulting_resolution,[],[f1326,f1436,f1295,f853])).

fof(f853,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f718])).

fof(f718,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f521])).

fof(f521,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f1295,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f835,f836])).

fof(f835,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f459])).

fof(f459,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f1436,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl31_8 ),
    inference(avatar_component_clause,[],[f1434])).

% (16473)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f1434,plain,
    ( spl31_8
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_8])])).

fof(f1819,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl31_9
    | ~ spl31_14 ),
    inference(backward_demodulation,[],[f1567,f1816])).

fof(f1816,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl31_14 ),
    inference(unit_resulting_resolution,[],[f1774,f850])).

fof(f850,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f520])).

fof(f520,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1774,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl31_14 ),
    inference(avatar_component_clause,[],[f1772])).

fof(f1772,plain,
    ( spl31_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_14])])).

fof(f1567,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))
    | ~ spl31_9 ),
    inference(forward_demodulation,[],[f1566,f1013])).

fof(f1013,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1566,plain,
    ( r1_tarski(k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl31_9 ),
    inference(forward_demodulation,[],[f1551,f979])).

fof(f979,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1551,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))
    | ~ spl31_9 ),
    inference(unit_resulting_resolution,[],[f1237,f1546,f842])).

fof(f842,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f514])).

fof(f514,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f513])).

fof(f513,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1546,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl31_9 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1544,plain,
    ( spl31_9
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_9])])).

fof(f1237,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f848])).

fof(f848,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f717])).

fof(f717,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f716])).

fof(f716,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1775,plain,
    ( spl31_14
    | ~ spl31_1 ),
    inference(avatar_split_clause,[],[f1764,f1324,f1772])).

fof(f1764,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl31_1 ),
    inference(forward_demodulation,[],[f1759,f1301])).

fof(f1759,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k1_xboole_0))
    | ~ spl31_1 ),
    inference(unit_resulting_resolution,[],[f1326,f1295,f946,f855])).

fof(f855,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f525])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f524])).

fof(f524,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f946,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1547,plain,
    ( spl31_9
    | ~ spl31_1
    | ~ spl31_3 ),
    inference(avatar_split_clause,[],[f1532,f1334,f1324,f1544])).

fof(f1334,plain,
    ( spl31_3
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_3])])).

fof(f1532,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl31_1
    | ~ spl31_3 ),
    inference(backward_demodulation,[],[f1336,f1525])).

fof(f1336,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl31_3 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1437,plain,
    ( ~ spl31_8
    | spl31_4 ),
    inference(avatar_split_clause,[],[f1417,f1338,f1434])).

fof(f1338,plain,
    ( spl31_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_4])])).

fof(f1417,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl31_4 ),
    inference(unit_resulting_resolution,[],[f1339,f946,f849])).

fof(f849,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f717])).

fof(f1339,plain,
    ( k1_xboole_0 != sK1
    | spl31_4 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1346,plain,(
    ~ spl31_4 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | ~ spl31_4 ),
    inference(subsumption_resolution,[],[f1344,f1340])).

fof(f1340,plain,
    ( k1_xboole_0 = sK1
    | ~ spl31_4 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1344,plain,
    ( k1_xboole_0 != sK1
    | ~ spl31_4 ),
    inference(subsumption_resolution,[],[f1343,f946])).

fof(f1343,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | k1_xboole_0 != sK1
    | ~ spl31_4 ),
    inference(backward_demodulation,[],[f1294,f1340])).

fof(f1294,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f833,f836])).

fof(f833,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f713])).

fof(f713,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f711,f712])).

fof(f712,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f711,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f710])).

fof(f710,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f508])).

fof(f508,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f500])).

fof(f500,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f499])).

fof(f499,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f1341,plain,
    ( spl31_3
    | spl31_4 ),
    inference(avatar_split_clause,[],[f1293,f1338,f1334])).

fof(f1293,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f832,f836])).

fof(f832,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f713])).

fof(f1327,plain,(
    spl31_1 ),
    inference(avatar_split_clause,[],[f831,f1324])).

fof(f831,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f713])).
%------------------------------------------------------------------------------

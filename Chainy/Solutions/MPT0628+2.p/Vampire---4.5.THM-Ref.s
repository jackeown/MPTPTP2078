%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0628+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 588 expanded)
%              Number of leaves         :   34 ( 214 expanded)
%              Depth                    :   10
%              Number of atoms          :  515 (3053 expanded)
%              Number of equality atoms :   71 ( 541 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2293,f2297,f2301,f2305,f2309,f2313,f2321,f2322,f2326,f2334,f2351,f2352,f2355,f2361,f2369,f2376,f2378,f2380,f2382,f2386,f2388,f2398,f2403,f2409,f2417,f2419])).

fof(f2419,plain,
    ( spl91_14
    | spl91_17 ),
    inference(avatar_contradiction_clause,[],[f2418])).

fof(f2418,plain,
    ( $false
    | spl91_14
    | spl91_17 ),
    inference(global_subsumption,[],[f1543,f1542,f2397,f2414])).

fof(f2414,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_14 ),
    inference(trivial_inequality_removal,[],[f2413])).

fof(f2413,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_14 ),
    inference(superposition,[],[f2350,f2201])).

fof(f2201,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1568])).

fof(f1568,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1309])).

fof(f1309,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f939])).

fof(f939,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f938])).

fof(f938,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2350,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | spl91_14 ),
    inference(avatar_component_clause,[],[f2349])).

fof(f2349,plain,
    ( spl91_14
  <=> k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_14])])).

fof(f2397,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | spl91_17 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2396,plain,
    ( spl91_17
  <=> r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_17])])).

fof(f1542,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1298])).

fof(f1298,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f923,f1297,f1296])).

fof(f1296,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
            & r2_hidden(X0,k1_relat_1(X1))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0))
          & r2_hidden(sK0,k1_relat_1(sK1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1297,plain,
    ( ? [X2] :
        ( k1_funct_1(k5_relat_1(sK1,X2),sK0) != k1_funct_1(X2,k1_funct_1(sK1,sK0))
        & r2_hidden(sK0,k1_relat_1(sK1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f923,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f922])).

fof(f922,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f913])).

fof(f913,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(X1))
             => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f912])).

fof(f912,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f1543,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1298])).

fof(f2417,plain,
    ( spl91_14
    | spl91_17 ),
    inference(avatar_contradiction_clause,[],[f2416])).

fof(f2416,plain,
    ( $false
    | spl91_14
    | spl91_17 ),
    inference(global_subsumption,[],[f1543,f1542,f2397,f2415])).

fof(f2415,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_14 ),
    inference(trivial_inequality_removal,[],[f2412])).

fof(f2412,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_14 ),
    inference(superposition,[],[f2350,f2202])).

fof(f2202,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1567])).

fof(f1567,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1309])).

fof(f2409,plain,
    ( ~ spl91_11
    | ~ spl91_19
    | ~ spl91_9
    | spl91_13 ),
    inference(avatar_split_clause,[],[f2393,f2346,f2329,f2406,f2340])).

fof(f2340,plain,
    ( spl91_11
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_11])])).

fof(f2406,plain,
    ( spl91_19
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_19])])).

fof(f2329,plain,
    ( spl91_9
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_9])])).

fof(f2346,plain,
    ( spl91_13
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_13])])).

fof(f2393,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl91_13 ),
    inference(superposition,[],[f2354,f1750])).

fof(f1750,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1036])).

fof(f1036,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f860])).

fof(f860,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f2354,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | spl91_13 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2403,plain,
    ( ~ spl91_18
    | spl91_13 ),
    inference(avatar_split_clause,[],[f2399,f2346,f2401])).

fof(f2401,plain,
    ( spl91_18
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_18])])).

fof(f2399,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | spl91_13 ),
    inference(global_subsumption,[],[f1544,f1542,f1540,f2390])).

fof(f2390,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl91_13 ),
    inference(superposition,[],[f2354,f1607])).

fof(f1607,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f974])).

fof(f974,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f973])).

fof(f973,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f1540,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1298])).

fof(f1544,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1298])).

fof(f2398,plain,
    ( ~ spl91_17
    | spl91_13 ),
    inference(avatar_split_clause,[],[f2394,f2346,f2396])).

fof(f2394,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | spl91_13 ),
    inference(global_subsumption,[],[f1544,f1543,f1542,f1541,f1540,f2389])).

fof(f2389,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_13 ),
    inference(resolution,[],[f2354,f1555])).

fof(f1555,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1304])).

fof(f1304,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1303])).

fof(f1303,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f928])).

fof(f928,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f927])).

fof(f927,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f910])).

fof(f910,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f1541,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1298])).

fof(f2388,plain,(
    spl91_12 ),
    inference(avatar_contradiction_clause,[],[f2387])).

fof(f2387,plain,
    ( $false
    | spl91_12 ),
    inference(global_subsumption,[],[f1543,f1542,f1541,f1540,f2383])).

fof(f2383,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl91_12 ),
    inference(resolution,[],[f2344,f1636])).

fof(f1636,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f993,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f992])).

fof(f992,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f895])).

fof(f895,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f2344,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | spl91_12 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f2343,plain,
    ( spl91_12
  <=> v1_funct_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_12])])).

fof(f2386,plain,(
    spl91_12 ),
    inference(avatar_contradiction_clause,[],[f2385])).

fof(f2385,plain,
    ( $false
    | spl91_12 ),
    inference(global_subsumption,[],[f1543,f1542,f1541,f1540,f2383])).

fof(f2382,plain,(
    spl91_11 ),
    inference(avatar_contradiction_clause,[],[f2381])).

fof(f2381,plain,
    ( $false
    | spl91_11 ),
    inference(global_subsumption,[],[f1542,f1540,f2373])).

fof(f2373,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl91_11 ),
    inference(resolution,[],[f2341,f1583])).

fof(f1583,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f947])).

fof(f947,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f946])).

fof(f946,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2341,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl91_11 ),
    inference(avatar_component_clause,[],[f2340])).

fof(f2380,plain,(
    spl91_11 ),
    inference(avatar_contradiction_clause,[],[f2379])).

fof(f2379,plain,
    ( $false
    | spl91_11 ),
    inference(global_subsumption,[],[f1542,f1540,f2373])).

fof(f2378,plain,(
    spl91_11 ),
    inference(avatar_contradiction_clause,[],[f2377])).

fof(f2377,plain,
    ( $false
    | spl91_11 ),
    inference(global_subsumption,[],[f1543,f1542,f1541,f1540,f2370])).

fof(f2370,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl91_11 ),
    inference(resolution,[],[f2341,f1635])).

fof(f1635,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f2376,plain,(
    spl91_11 ),
    inference(avatar_contradiction_clause,[],[f2375])).

fof(f2375,plain,
    ( $false
    | spl91_11 ),
    inference(global_subsumption,[],[f1543,f1542,f1541,f1540,f2370])).

fof(f2369,plain,
    ( ~ spl91_16
    | spl91_10 ),
    inference(avatar_split_clause,[],[f2365,f2332,f2367])).

fof(f2367,plain,
    ( spl91_16
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_16])])).

fof(f2332,plain,
    ( spl91_10
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_10])])).

fof(f2365,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | spl91_10 ),
    inference(global_subsumption,[],[f1540,f2364])).

fof(f2364,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl91_10 ),
    inference(trivial_inequality_removal,[],[f2363])).

fof(f2363,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl91_10 ),
    inference(superposition,[],[f2333,f1749])).

fof(f1749,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1423])).

fof(f2333,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl91_10 ),
    inference(avatar_component_clause,[],[f2332])).

fof(f2361,plain,
    ( ~ spl91_15
    | spl91_7 ),
    inference(avatar_split_clause,[],[f2356,f2319,f2359])).

fof(f2359,plain,
    ( spl91_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_15])])).

fof(f2319,plain,
    ( spl91_7
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_7])])).

fof(f2356,plain,
    ( ~ v1_xboole_0(sK1)
    | spl91_7 ),
    inference(resolution,[],[f2320,f1819])).

fof(f1819,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1070])).

fof(f1070,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f680])).

fof(f680,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f2320,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | spl91_7 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f2355,plain,
    ( ~ spl91_13
    | spl91_1 ),
    inference(avatar_split_clause,[],[f2353,f2291,f2346])).

fof(f2291,plain,
    ( spl91_1
  <=> k1_funct_1(k5_relat_1(sK1,sK2),sK0) = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_1])])).

fof(f2353,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | spl91_1 ),
    inference(global_subsumption,[],[f1543,f1542,f1541,f1540,f2338])).

fof(f2338,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_1 ),
    inference(trivial_inequality_removal,[],[f2337])).

fof(f2337,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl91_1 ),
    inference(superposition,[],[f2292,f1556])).

fof(f1556,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f929])).

fof(f929,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f911])).

fof(f911,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f2292,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | spl91_1 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f2352,plain,
    ( ~ spl91_11
    | ~ spl91_12
    | spl91_13
    | ~ spl91_14
    | spl91_1 ),
    inference(avatar_split_clause,[],[f2336,f2291,f2349,f2346,f2343,f2340])).

fof(f2336,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl91_1 ),
    inference(superposition,[],[f2292,f2201])).

fof(f2351,plain,
    ( ~ spl91_11
    | ~ spl91_12
    | spl91_13
    | ~ spl91_14
    | spl91_1 ),
    inference(avatar_split_clause,[],[f2335,f2291,f2349,f2346,f2343,f2340])).

fof(f2335,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl91_1 ),
    inference(superposition,[],[f2292,f2202])).

fof(f2334,plain,
    ( spl91_9
    | ~ spl91_10
    | ~ spl91_2 ),
    inference(avatar_split_clause,[],[f2327,f2295,f2332,f2329])).

fof(f2295,plain,
    ( spl91_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_2])])).

fof(f2327,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ spl91_2 ),
    inference(global_subsumption,[],[f1540,f2317])).

fof(f2317,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl91_2 ),
    inference(superposition,[],[f2296,f1750])).

fof(f2296,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl91_2 ),
    inference(avatar_component_clause,[],[f2295])).

fof(f2326,plain,
    ( ~ spl91_8
    | ~ spl91_2 ),
    inference(avatar_split_clause,[],[f2316,f2295,f2324])).

fof(f2324,plain,
    ( spl91_8
  <=> r2_hidden(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_8])])).

fof(f2316,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK0)
    | ~ spl91_2 ),
    inference(resolution,[],[f2296,f1620])).

fof(f1620,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f983])).

fof(f983,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2322,plain,
    ( ~ spl91_7
    | ~ spl91_2 ),
    inference(avatar_split_clause,[],[f2315,f2295,f2319])).

fof(f2315,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl91_2 ),
    inference(resolution,[],[f2296,f1801])).

fof(f1801,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1056])).

fof(f1056,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2321,plain,
    ( ~ spl91_7
    | ~ spl91_2 ),
    inference(avatar_split_clause,[],[f2314,f2295,f2319])).

fof(f2314,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl91_2 ),
    inference(resolution,[],[f2296,f1814])).

fof(f1814,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1452])).

fof(f1452,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK73(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK73])],[f1450,f1451])).

fof(f1451,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK73(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1450,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1449])).

fof(f1449,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2313,plain,(
    spl91_6 ),
    inference(avatar_split_clause,[],[f1540,f2311])).

fof(f2311,plain,
    ( spl91_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_6])])).

fof(f2309,plain,(
    spl91_5 ),
    inference(avatar_split_clause,[],[f1541,f2307])).

fof(f2307,plain,
    ( spl91_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_5])])).

fof(f2305,plain,(
    spl91_4 ),
    inference(avatar_split_clause,[],[f1542,f2303])).

fof(f2303,plain,
    ( spl91_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_4])])).

fof(f2301,plain,(
    spl91_3 ),
    inference(avatar_split_clause,[],[f1543,f2299])).

fof(f2299,plain,
    ( spl91_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_3])])).

fof(f2297,plain,(
    spl91_2 ),
    inference(avatar_split_clause,[],[f1544,f2295])).

fof(f2293,plain,(
    ~ spl91_1 ),
    inference(avatar_split_clause,[],[f1545,f2291])).

fof(f1545,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1298])).
%------------------------------------------------------------------------------

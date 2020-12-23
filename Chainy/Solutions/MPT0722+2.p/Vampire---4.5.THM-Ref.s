%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0722+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   45 (  89 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 341 expanded)
%              Number of equality atoms :   26 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2551,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1343,f1347,f1351,f1355,f1359,f2189,f2536])).

fof(f2536,plain,
    ( ~ spl21_2
    | ~ spl21_3
    | ~ spl21_4
    | ~ spl21_5
    | spl21_83 ),
    inference(avatar_contradiction_clause,[],[f2523])).

fof(f2523,plain,
    ( $false
    | ~ spl21_2
    | ~ spl21_3
    | ~ spl21_4
    | ~ spl21_5
    | spl21_83 ),
    inference(unit_resulting_resolution,[],[f1358,f1354,f1350,f1346,f2188,f1288])).

fof(f1288,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1129])).

fof(f1129,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1128])).

fof(f1128,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f985])).

fof(f985,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f2188,plain,
    ( sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1))
    | spl21_83 ),
    inference(avatar_component_clause,[],[f2187])).

fof(f2187,plain,
    ( spl21_83
  <=> sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_83])])).

fof(f1346,plain,
    ( r1_tarski(sK1,k1_relat_1(sK0))
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1345,plain,
    ( spl21_2
  <=> r1_tarski(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f1350,plain,
    ( v2_funct_1(sK0)
    | ~ spl21_3 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1349,plain,
    ( spl21_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_3])])).

fof(f1354,plain,
    ( v1_funct_1(sK0)
    | ~ spl21_4 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1353,plain,
    ( spl21_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_4])])).

fof(f1358,plain,
    ( v1_relat_1(sK0)
    | ~ spl21_5 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1357,plain,
    ( spl21_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_5])])).

fof(f2189,plain,
    ( ~ spl21_83
    | spl21_1
    | ~ spl21_3
    | ~ spl21_4
    | ~ spl21_5 ),
    inference(avatar_split_clause,[],[f2172,f1357,f1353,f1349,f1341,f2187])).

fof(f1341,plain,
    ( spl21_1
  <=> sK1 = k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_1])])).

fof(f2172,plain,
    ( sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1))
    | spl21_1
    | ~ spl21_3
    | ~ spl21_4
    | ~ spl21_5 ),
    inference(superposition,[],[f1342,f1918])).

fof(f1918,plain,
    ( ! [X7] : k9_relat_1(k2_funct_1(sK0),X7) = k10_relat_1(sK0,X7)
    | ~ spl21_3
    | ~ spl21_4
    | ~ spl21_5 ),
    inference(subsumption_resolution,[],[f1917,f1358])).

fof(f1917,plain,
    ( ! [X7] :
        ( k9_relat_1(k2_funct_1(sK0),X7) = k10_relat_1(sK0,X7)
        | ~ v1_relat_1(sK0) )
    | ~ spl21_3
    | ~ spl21_4 ),
    inference(subsumption_resolution,[],[f1912,f1354])).

fof(f1912,plain,
    ( ! [X7] :
        ( k9_relat_1(k2_funct_1(sK0),X7) = k10_relat_1(sK0,X7)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl21_3 ),
    inference(resolution,[],[f1239,f1350])).

fof(f1239,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1092])).

fof(f1092,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1091])).

fof(f1091,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f975])).

fof(f975,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f1342,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    | spl21_1 ),
    inference(avatar_component_clause,[],[f1341])).

fof(f1359,plain,(
    spl21_5 ),
    inference(avatar_split_clause,[],[f1205,f1357])).

fof(f1205,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1160])).

fof(f1160,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1057,f1159,f1158])).

fof(f1158,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1159,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1057,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1056])).

fof(f1056,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1000])).

fof(f1000,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f999])).

fof(f999,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f1355,plain,(
    spl21_4 ),
    inference(avatar_split_clause,[],[f1206,f1353])).

fof(f1206,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1160])).

fof(f1351,plain,(
    spl21_3 ),
    inference(avatar_split_clause,[],[f1207,f1349])).

fof(f1207,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1160])).

fof(f1347,plain,(
    spl21_2 ),
    inference(avatar_split_clause,[],[f1208,f1345])).

fof(f1208,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f1160])).

fof(f1343,plain,(
    ~ spl21_1 ),
    inference(avatar_split_clause,[],[f1209,f1341])).

fof(f1209,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1160])).
%------------------------------------------------------------------------------

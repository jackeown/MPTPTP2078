%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0755+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 120 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 647 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1338,f1342,f1346,f1350,f1354,f1358,f1392,f1578,f1586,f1718])).

fof(f1718,plain,
    ( spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f1717])).

fof(f1717,plain,
    ( $false
    | spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f1716,f1357])).

fof(f1357,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f1356])).

fof(f1356,plain,
    ( spl12_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f1716,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f1715,f1349])).

fof(f1349,plain,
    ( v1_funct_1(sK1)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f1348])).

fof(f1348,plain,
    ( spl12_7
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f1715,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl12_4
    | ~ spl12_5
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f1714,f1345])).

fof(f1345,plain,
    ( v5_ordinal1(sK1)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1344,plain,
    ( spl12_6
  <=> v5_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f1714,plain,
    ( ~ v5_ordinal1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl12_4
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f1707,f1341])).

fof(f1341,plain,
    ( v3_ordinal1(sK2)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f1340])).

fof(f1340,plain,
    ( spl12_5
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f1707,plain,
    ( ~ v3_ordinal1(sK2)
    | ~ v5_ordinal1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl12_4 ),
    inference(resolution,[],[f1293,f1337])).

fof(f1337,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1336,plain,
    ( spl12_4
  <=> v5_ordinal1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f1293,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(k7_relat_1(X0,X1))
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1177])).

fof(f1177,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1176])).

fof(f1176,plain,(
    ! [X0,X1] :
      ( ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v3_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1073])).

fof(f1073,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v5_ordinal1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v5_ordinal1(k7_relat_1(X0,X1))
        & v5_relat_1(k7_relat_1(X0,X1),k2_relat_1(X0))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(f1586,plain,
    ( spl12_3
    | ~ spl12_7
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f1585])).

fof(f1585,plain,
    ( $false
    | spl12_3
    | ~ spl12_7
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f1584,f1357])).

fof(f1584,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_3
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f1582,f1349])).

fof(f1582,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl12_3 ),
    inference(resolution,[],[f1334,f1247])).

fof(f1247,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1135])).

fof(f1135,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1134])).

fof(f1134,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f926])).

fof(f926,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f1334,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f1333])).

fof(f1333,plain,
    ( spl12_3
  <=> v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f1578,plain,
    ( spl12_2
    | ~ spl12_8
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | spl12_2
    | ~ spl12_8
    | ~ spl12_9 ),
    inference(unit_resulting_resolution,[],[f1357,f1353,f1331,f1316])).

fof(f1316,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X1)
      | v5_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f1184])).

fof(f1184,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1183])).

fof(f1183,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1070])).

fof(f1070,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f1331,plain,
    ( ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f1330,plain,
    ( spl12_2
  <=> v5_relat_1(k7_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1353,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1352,plain,
    ( spl12_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f1392,plain,
    ( spl12_1
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f1391])).

fof(f1391,plain,
    ( $false
    | spl12_1
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f1388,f1357])).

fof(f1388,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_1 ),
    inference(resolution,[],[f1265,f1328])).

fof(f1328,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f1327,plain,
    ( spl12_1
  <=> v1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1158])).

fof(f1158,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1358,plain,(
    spl12_9 ),
    inference(avatar_split_clause,[],[f1226,f1356])).

fof(f1226,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1200,plain,
    ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
      | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
    & v3_ordinal1(sK2)
    & v5_ordinal1(sK1)
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1117,f1199,f1198])).

fof(f1198,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
              | ~ v1_funct_1(k7_relat_1(X1,X2))
              | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
              | ~ v1_relat_1(k7_relat_1(X1,X2)) )
            & v3_ordinal1(X2) )
        & v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
            | ~ v1_funct_1(k7_relat_1(sK1,X2))
            | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
            | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(sK1)
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1199,plain,
    ( ? [X2] :
        ( ( ~ v5_ordinal1(k7_relat_1(sK1,X2))
          | ~ v1_funct_1(k7_relat_1(sK1,X2))
          | ~ v5_relat_1(k7_relat_1(sK1,X2),sK0)
          | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
        & v3_ordinal1(X2) )
   => ( ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1117,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1116])).

fof(f1116,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(k7_relat_1(X1,X2))
            | ~ v1_funct_1(k7_relat_1(X1,X2))
            | ~ v5_relat_1(k7_relat_1(X1,X2),X0)
            | ~ v1_relat_1(k7_relat_1(X1,X2)) )
          & v3_ordinal1(X2) )
      & v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1110])).

% (11456)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
fof(f1110,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( v5_ordinal1(k7_relat_1(X1,X2))
              & v1_funct_1(k7_relat_1(X1,X2))
              & v5_relat_1(k7_relat_1(X1,X2),X0)
              & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1109])).

fof(f1109,conjecture,(
    ! [X0,X1] :
      ( ( v5_ordinal1(X1)
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( v5_ordinal1(k7_relat_1(X1,X2))
            & v1_funct_1(k7_relat_1(X1,X2))
            & v5_relat_1(k7_relat_1(X1,X2),X0)
            & v1_relat_1(k7_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_ordinal1)).

fof(f1354,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f1227,f1352])).

fof(f1227,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1350,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f1228,f1348])).

fof(f1228,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1346,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f1229,f1344])).

fof(f1229,plain,(
    v5_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1342,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f1230,f1340])).

fof(f1230,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1338,plain,
    ( ~ spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f1231,f1336,f1333,f1330,f1327])).

fof(f1231,plain,
    ( ~ v5_ordinal1(k7_relat_1(sK1,sK2))
    | ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | ~ v5_relat_1(k7_relat_1(sK1,sK2),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f1200])).

% (11436)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
%------------------------------------------------------------------------------

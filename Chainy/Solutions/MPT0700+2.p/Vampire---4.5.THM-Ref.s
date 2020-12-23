%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0700+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 257 expanded)
%              Number of leaves         :    7 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 980 expanded)
%              Number of equality atoms :   32 ( 235 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2098,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1648,f2097])).

fof(f2097,plain,(
    ! [X8] : k10_relat_1(sK1,X8) = k9_relat_1(k4_relat_1(sK1),X8) ),
    inference(forward_demodulation,[],[f2096,f1647])).

fof(f1647,plain,(
    sK1 = k2_funct_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1632,f1646])).

fof(f1646,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1645,f1236])).

fof(f1236,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1161])).

fof(f1161,plain,
    ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1016,f1160])).

fof(f1160,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1016,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1015])).

fof(f1015,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,X0) != k9_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f957])).

fof(f957,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f956])).

fof(f956,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f1645,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1641,f1237])).

fof(f1237,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1161])).

fof(f1641,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1326,f1238])).

fof(f1238,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1161])).

fof(f1326,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1096])).

fof(f1096,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1095])).

fof(f1095,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f1632,plain,(
    sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f1631,f1236])).

fof(f1631,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1627,f1237])).

fof(f1627,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1325,f1238])).

fof(f1325,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1094])).

fof(f1094,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1093])).

fof(f1093,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f996])).

fof(f996,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f2096,plain,(
    ! [X8] : k9_relat_1(k4_relat_1(sK1),X8) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X8) ),
    inference(subsumption_resolution,[],[f2095,f1661])).

fof(f1661,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1660,f1236])).

fof(f1660,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1654,f1237])).

fof(f1654,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f1328,f1646])).

fof(f1328,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1100])).

fof(f1100,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1099])).

fof(f1099,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f898])).

fof(f898,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f2095,plain,(
    ! [X8] :
      ( k9_relat_1(k4_relat_1(sK1),X8) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X8)
      | ~ v1_relat_1(k4_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f2089,f1659])).

fof(f1659,plain,(
    v1_funct_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1658,f1236])).

fof(f1658,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1653,f1237])).

fof(f1653,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f1329,f1646])).

fof(f1329,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1100])).

fof(f2089,plain,(
    ! [X8] :
      ( k9_relat_1(k4_relat_1(sK1),X8) = k10_relat_1(k2_funct_1(k4_relat_1(sK1)),X8)
      | ~ v1_funct_1(k4_relat_1(sK1))
      | ~ v1_relat_1(k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f1295,f1657])).

fof(f1657,plain,(
    v2_funct_1(k4_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1656,f1236])).

fof(f1656,plain,
    ( v2_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1655,f1237])).

fof(f1655,plain,
    ( v2_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1652,f1238])).

fof(f1652,plain,
    ( v2_funct_1(k4_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f1327,f1646])).

fof(f1327,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1098])).

fof(f1098,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1097])).

fof(f1097,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f993])).

fof(f993,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f1295,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1074])).

fof(f1074,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f955])).

fof(f955,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f1648,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k4_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f1239,f1646])).

fof(f1239,plain,(
    k10_relat_1(sK1,sK0) != k9_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f1161])).
%------------------------------------------------------------------------------

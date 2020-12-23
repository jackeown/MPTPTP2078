%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0939+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:59 EST 2020

% Result     : Theorem 5.29s
% Output     : Refutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 207 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 ( 688 expanded)
%              Number of equality atoms :   13 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1605,f1610,f1615,f1626,f1637,f1638,f1639,f1640,f4576])).

fof(f4576,plain,
    ( ~ spl19_1
    | spl19_2 ),
    inference(avatar_contradiction_clause,[],[f4575])).

fof(f4575,plain,
    ( $false
    | ~ spl19_1
    | spl19_2 ),
    inference(subsumption_resolution,[],[f4574,f1604])).

fof(f1604,plain,
    ( v3_ordinal1(sK0)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f1602,plain,
    ( spl19_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f4574,plain,
    ( ~ v3_ordinal1(sK0)
    | spl19_2 ),
    inference(resolution,[],[f4529,f1609])).

fof(f1609,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    | spl19_2 ),
    inference(avatar_component_clause,[],[f1607])).

fof(f1607,plain,
    ( spl19_2
  <=> v6_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f4529,plain,(
    ! [X4] :
      ( v6_relat_2(k1_wellord2(X4))
      | ~ v3_ordinal1(X4) ) ),
    inference(global_subsumption,[],[f2328,f2382,f3772])).

fof(f3772,plain,(
    ! [X13] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X13)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X13)))
      | v6_relat_2(k1_wellord2(X13)) ) ),
    inference(subsumption_resolution,[],[f3705,f1936])).

fof(f1936,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | v6_relat_2(k1_wellord2(X3)) ) ),
    inference(subsumption_resolution,[],[f1935,f1677])).

fof(f1677,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f1673,f1516])).

fof(f1516,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1422])).

fof(f1422,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1673,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f1503,f1660])).

fof(f1660,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f1592,f1516])).

fof(f1592,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f1515])).

fof(f1515,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1440])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1439])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1420])).

fof(f1420,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f1503,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f1437])).

fof(f1437,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1150])).

fof(f1150,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f1935,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | v6_relat_2(k1_wellord2(X3)) ) ),
    inference(subsumption_resolution,[],[f1934,f1678])).

fof(f1678,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k1_wellord2(X1)),X1)
      | v6_relat_2(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f1674,f1516])).

fof(f1674,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k1_wellord2(X1)),X1)
      | ~ v1_relat_1(k1_wellord2(X1))
      | v6_relat_2(k1_wellord2(X1)) ) ),
    inference(superposition,[],[f1502,f1660])).

fof(f1502,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f1437])).

fof(f1934,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | v6_relat_2(k1_wellord2(X3)) ) ),
    inference(subsumption_resolution,[],[f1932,f1516])).

fof(f1932,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | ~ v1_relat_1(k1_wellord2(X3))
      | v6_relat_2(k1_wellord2(X3)) ) ),
    inference(duplicate_literal_removal,[],[f1928])).

fof(f1928,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | ~ v1_relat_1(k1_wellord2(X3))
      | ~ v1_relat_1(k1_wellord2(X3))
      | v6_relat_2(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f1598,f1505])).

fof(f1505,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f1437])).

fof(f1598,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f1509])).

fof(f1509,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1440])).

fof(f3705,plain,(
    ! [X13] :
      ( r1_tarski(sK1(k1_wellord2(X13)),sK2(k1_wellord2(X13)))
      | ~ v3_ordinal1(sK2(k1_wellord2(X13)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X13)))
      | v6_relat_2(k1_wellord2(X13)) ) ),
    inference(resolution,[],[f2226,f1939])).

fof(f1939,plain,(
    ! [X4] :
      ( ~ r1_tarski(sK2(k1_wellord2(X4)),sK1(k1_wellord2(X4)))
      | v6_relat_2(k1_wellord2(X4)) ) ),
    inference(subsumption_resolution,[],[f1938,f1678])).

fof(f1938,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK1(k1_wellord2(X4)),X4)
      | ~ r1_tarski(sK2(k1_wellord2(X4)),sK1(k1_wellord2(X4)))
      | v6_relat_2(k1_wellord2(X4)) ) ),
    inference(subsumption_resolution,[],[f1937,f1677])).

fof(f1937,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2(k1_wellord2(X4)),X4)
      | ~ r2_hidden(sK1(k1_wellord2(X4)),X4)
      | ~ r1_tarski(sK2(k1_wellord2(X4)),sK1(k1_wellord2(X4)))
      | v6_relat_2(k1_wellord2(X4)) ) ),
    inference(subsumption_resolution,[],[f1931,f1516])).

fof(f1931,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2(k1_wellord2(X4)),X4)
      | ~ r2_hidden(sK1(k1_wellord2(X4)),X4)
      | ~ r1_tarski(sK2(k1_wellord2(X4)),sK1(k1_wellord2(X4)))
      | ~ v1_relat_1(k1_wellord2(X4))
      | v6_relat_2(k1_wellord2(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1929])).

fof(f1929,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK2(k1_wellord2(X4)),X4)
      | ~ r2_hidden(sK1(k1_wellord2(X4)),X4)
      | ~ r1_tarski(sK2(k1_wellord2(X4)),sK1(k1_wellord2(X4)))
      | ~ v1_relat_1(k1_wellord2(X4))
      | ~ v1_relat_1(k1_wellord2(X4))
      | v6_relat_2(k1_wellord2(X4)) ) ),
    inference(resolution,[],[f1598,f1506])).

fof(f1506,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f1437])).

fof(f2226,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f2205])).

fof(f2205,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f1697,f1528])).

fof(f1528,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1446])).

fof(f1446,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1445])).

fof(f1445,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1083])).

fof(f1083,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f1697,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1692])).

fof(f1692,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f1529,f1528])).

fof(f1529,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1448])).

fof(f1448,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1447])).

fof(f1447,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1059])).

fof(f1059,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f2382,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | v3_ordinal1(sK1(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f1678,f1537])).

fof(f1537,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f1455])).

fof(f1455,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f1454])).

fof(f1454,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1096])).

fof(f1096,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f2328,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | v3_ordinal1(sK2(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f1677,f1537])).

fof(f1640,plain,
    ( ~ spl19_1
    | ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1632])).

fof(f1632,plain,
    ( $false
    | ~ spl19_1
    | ~ spl19_4 ),
    inference(resolution,[],[f1622,f1604])).

fof(f1622,plain,
    ( ! [X1] : ~ v3_ordinal1(X1)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1621,plain,
    ( spl19_4
  <=> ! [X1] : ~ v3_ordinal1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f1639,plain,
    ( ~ spl19_3
    | ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1633])).

fof(f1633,plain,
    ( $false
    | ~ spl19_3
    | ~ spl19_4 ),
    inference(resolution,[],[f1622,f1614])).

fof(f1614,plain,
    ( v3_ordinal1(sK5)
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1612,plain,
    ( spl19_3
  <=> v3_ordinal1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f1638,plain,(
    ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1634])).

fof(f1634,plain,
    ( $false
    | ~ spl19_4 ),
    inference(resolution,[],[f1622,f1542])).

fof(f1542,plain,(
    ! [X0] : v3_ordinal1(sK9(X0)) ),
    inference(cnf_transformation,[],[f1457])).

fof(f1457,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f1456])).

fof(f1456,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r1_ordinal1(X1,X2)
          | r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1110])).

fof(f1110,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( v3_ordinal1(X2)
         => ( ~ r2_hidden(X2,X0)
           => r1_ordinal1(X1,X2) ) )
      & ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_ordinal1)).

fof(f1637,plain,(
    ~ spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1635])).

fof(f1635,plain,
    ( $false
    | ~ spl19_4 ),
    inference(resolution,[],[f1622,f1546])).

fof(f1546,plain,(
    ! [X0] : v3_ordinal1(sK11(X0)) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1459,plain,(
    ! [X0] :
    ? [X1] :
      ( ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1109])).

fof(f1109,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f1626,plain,
    ( spl19_4
    | spl19_5 ),
    inference(avatar_split_clause,[],[f1530,f1624,f1621])).

fof(f1624,plain,
    ( spl19_5
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r1_ordinal1(X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f1530,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X0) ) ),
    inference(cnf_transformation,[],[f1450])).

fof(f1450,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f1449])).

fof(f1449,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1084])).

fof(f1084,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_ordinal1)).

fof(f1615,plain,(
    spl19_3 ),
    inference(avatar_split_clause,[],[f1519,f1612])).

fof(f1519,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f1080])).

fof(f1080,axiom,(
    ? [X0] : v3_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_ordinal1)).

fof(f1610,plain,(
    ~ spl19_2 ),
    inference(avatar_split_clause,[],[f1488,f1607])).

fof(f1488,plain,(
    ~ v6_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f1431])).

fof(f1431,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1428])).

fof(f1428,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f1427])).

fof(f1427,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_wellord2)).

fof(f1605,plain,(
    spl19_1 ),
    inference(avatar_split_clause,[],[f1487,f1602])).

fof(f1487,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f1431])).
%------------------------------------------------------------------------------

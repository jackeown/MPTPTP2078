%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:41 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 127 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 382 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f78,f85,f103,f115,f133,f159,f163])).

fof(f163,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f54,f44,f158,f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ~ sP3(X2)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X1) ) ),
    inference(general_splitting,[],[f33,f37_D])).

fof(f37,plain,(
    ! [X2,X0] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | sP3(X2) ) ),
    inference(cnf_transformation,[],[f37_D])).

fof(f37_D,plain,(
    ! [X2] :
      ( ! [X0] : v4_relat_1(k7_relat_1(X2,X0),X0)
    <=> ~ sP3(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f158,plain,
    ( sP3(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_14
  <=> sP3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f44,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f54,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f159,plain,
    ( spl5_14
    | spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f150,f130,f57,f156])).

fof(f57,plain,
    ( spl5_4
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f130,plain,
    ( spl5_12
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f150,plain,
    ( sP3(sK2)
    | spl5_4
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f144,f59])).

fof(f59,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f144,plain,
    ( v4_relat_1(sK2,sK1)
    | sP3(sK2)
    | ~ spl5_12 ),
    inference(superposition,[],[f37,f132])).

fof(f132,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f122,f112,f42,f130])).

fof(f112,plain,
    ( spl5_10
  <=> r1_tarski(sK2,k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f122,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(resolution,[],[f114,f63])).

fof(f63,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k7_relat_1(X1,X2))
      | k7_relat_1(X1,X2) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f114,plain,
    ( r1_tarski(sK2,k7_relat_1(sK2,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f106,f101,f47,f112])).

fof(f47,plain,
    ( spl5_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f101,plain,
    ( spl5_9
  <=> ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(sK2,X0))
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f106,plain,
    ( r1_tarski(sK2,k7_relat_1(sK2,sK1))
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r1_tarski(sK2,k7_relat_1(sK2,X0)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f97,f82,f42,f101])).

fof(f82,plain,
    ( spl5_8
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f97,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(sK2,X0))
        | ~ r1_tarski(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f90,f44])).

fof(f90,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k7_relat_1(sK2,X0))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_8 ),
    inference(superposition,[],[f31,f84])).

fof(f84,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(f85,plain,
    ( spl5_8
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f80,f76,f52,f82])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f80,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f73,f42,f76])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f27,f44])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f60,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ~ v4_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v4_relat_1(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v4_relat_1(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v4_relat_1(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v4_relat_1(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v4_relat_1(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f55,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (792035328)
% 0.22/0.37  ipcrm: permission denied for id (795770882)
% 0.22/0.37  ipcrm: permission denied for id (792068101)
% 0.22/0.38  ipcrm: permission denied for id (792100870)
% 0.22/0.38  ipcrm: permission denied for id (792133639)
% 0.22/0.38  ipcrm: permission denied for id (792166408)
% 0.22/0.38  ipcrm: permission denied for id (792199177)
% 0.22/0.38  ipcrm: permission denied for id (799965194)
% 0.22/0.38  ipcrm: permission denied for id (792264715)
% 0.22/0.38  ipcrm: permission denied for id (799997964)
% 0.22/0.38  ipcrm: permission denied for id (792330253)
% 0.22/0.39  ipcrm: permission denied for id (798523407)
% 0.22/0.39  ipcrm: permission denied for id (792395792)
% 0.22/0.39  ipcrm: permission denied for id (798588946)
% 0.22/0.39  ipcrm: permission denied for id (792461331)
% 0.22/0.39  ipcrm: permission denied for id (798621716)
% 0.22/0.39  ipcrm: permission denied for id (796098581)
% 0.22/0.39  ipcrm: permission denied for id (796131350)
% 0.22/0.40  ipcrm: permission denied for id (800129047)
% 0.22/0.40  ipcrm: permission denied for id (796196888)
% 0.22/0.40  ipcrm: permission denied for id (796295193)
% 0.22/0.40  ipcrm: permission denied for id (796262426)
% 0.22/0.40  ipcrm: permission denied for id (792723484)
% 0.22/0.40  ipcrm: permission denied for id (796360733)
% 0.22/0.40  ipcrm: permission denied for id (792789022)
% 0.22/0.41  ipcrm: permission denied for id (798720031)
% 0.22/0.41  ipcrm: permission denied for id (800194592)
% 0.22/0.41  ipcrm: permission denied for id (800260130)
% 0.22/0.41  ipcrm: permission denied for id (796557348)
% 0.22/0.41  ipcrm: permission denied for id (796590117)
% 0.22/0.42  ipcrm: permission denied for id (793083943)
% 0.22/0.42  ipcrm: permission denied for id (793116712)
% 0.22/0.42  ipcrm: permission denied for id (793149481)
% 0.22/0.42  ipcrm: permission denied for id (793182250)
% 0.22/0.42  ipcrm: permission denied for id (793215019)
% 0.22/0.42  ipcrm: permission denied for id (793247788)
% 0.22/0.42  ipcrm: permission denied for id (793280557)
% 0.22/0.42  ipcrm: permission denied for id (793313326)
% 0.22/0.42  ipcrm: permission denied for id (798916655)
% 0.22/0.43  ipcrm: permission denied for id (793346096)
% 0.22/0.43  ipcrm: permission denied for id (793378865)
% 0.22/0.43  ipcrm: permission denied for id (793411634)
% 0.22/0.43  ipcrm: permission denied for id (793444403)
% 0.22/0.43  ipcrm: permission denied for id (793477172)
% 0.22/0.43  ipcrm: permission denied for id (793509941)
% 0.22/0.43  ipcrm: permission denied for id (793542710)
% 0.22/0.43  ipcrm: permission denied for id (796688439)
% 0.22/0.44  ipcrm: permission denied for id (798949432)
% 0.22/0.44  ipcrm: permission denied for id (793608249)
% 0.22/0.44  ipcrm: permission denied for id (793641018)
% 0.22/0.44  ipcrm: permission denied for id (798982203)
% 0.22/0.44  ipcrm: permission denied for id (793706556)
% 0.22/0.44  ipcrm: permission denied for id (800358461)
% 0.22/0.45  ipcrm: permission denied for id (796885056)
% 0.22/0.45  ipcrm: permission denied for id (799113281)
% 0.22/0.45  ipcrm: permission denied for id (800456770)
% 0.22/0.45  ipcrm: permission denied for id (796983363)
% 0.22/0.45  ipcrm: permission denied for id (799178820)
% 0.22/0.45  ipcrm: permission denied for id (797048901)
% 0.22/0.45  ipcrm: permission denied for id (799211590)
% 0.22/0.45  ipcrm: permission denied for id (797114439)
% 0.22/0.46  ipcrm: permission denied for id (799244360)
% 0.22/0.46  ipcrm: permission denied for id (797179977)
% 0.22/0.46  ipcrm: permission denied for id (797245515)
% 0.22/0.46  ipcrm: permission denied for id (797278284)
% 0.22/0.46  ipcrm: permission denied for id (797311053)
% 0.22/0.46  ipcrm: permission denied for id (797343822)
% 0.22/0.46  ipcrm: permission denied for id (800522319)
% 0.22/0.47  ipcrm: permission denied for id (797409360)
% 0.22/0.47  ipcrm: permission denied for id (799342673)
% 0.22/0.47  ipcrm: permission denied for id (799375442)
% 0.22/0.47  ipcrm: permission denied for id (797507667)
% 0.22/0.47  ipcrm: permission denied for id (794394709)
% 0.22/0.47  ipcrm: permission denied for id (797573206)
% 0.22/0.47  ipcrm: permission denied for id (799473752)
% 0.22/0.48  ipcrm: permission denied for id (797671513)
% 0.22/0.48  ipcrm: permission denied for id (797704282)
% 0.22/0.48  ipcrm: permission denied for id (797737051)
% 0.22/0.48  ipcrm: permission denied for id (800653405)
% 0.22/0.48  ipcrm: permission denied for id (794689630)
% 0.22/0.48  ipcrm: permission denied for id (797835359)
% 0.22/0.48  ipcrm: permission denied for id (794755168)
% 0.22/0.49  ipcrm: permission denied for id (797868129)
% 0.22/0.49  ipcrm: permission denied for id (794787938)
% 0.22/0.49  ipcrm: permission denied for id (794820707)
% 0.22/0.49  ipcrm: permission denied for id (794853476)
% 0.22/0.49  ipcrm: permission denied for id (794886245)
% 0.22/0.49  ipcrm: permission denied for id (794919014)
% 0.22/0.49  ipcrm: permission denied for id (794951783)
% 0.22/0.49  ipcrm: permission denied for id (794984552)
% 0.22/0.50  ipcrm: permission denied for id (797900905)
% 0.22/0.50  ipcrm: permission denied for id (795017322)
% 0.22/0.50  ipcrm: permission denied for id (795050091)
% 0.22/0.50  ipcrm: permission denied for id (795082860)
% 0.22/0.50  ipcrm: permission denied for id (795115629)
% 0.22/0.50  ipcrm: permission denied for id (795148398)
% 0.22/0.50  ipcrm: permission denied for id (795181167)
% 0.22/0.50  ipcrm: permission denied for id (799572080)
% 0.22/0.51  ipcrm: permission denied for id (799604849)
% 0.22/0.51  ipcrm: permission denied for id (799637618)
% 0.22/0.51  ipcrm: permission denied for id (799670387)
% 0.22/0.51  ipcrm: permission denied for id (798130293)
% 0.22/0.51  ipcrm: permission denied for id (798195831)
% 0.22/0.51  ipcrm: permission denied for id (795476088)
% 0.22/0.52  ipcrm: permission denied for id (795508857)
% 0.22/0.52  ipcrm: permission denied for id (795541626)
% 0.22/0.52  ipcrm: permission denied for id (795574395)
% 0.22/0.52  ipcrm: permission denied for id (795607164)
% 0.22/0.52  ipcrm: permission denied for id (799768701)
% 0.22/0.52  ipcrm: permission denied for id (799801470)
% 0.56/0.64  % (27517)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.56/0.64  % (27517)Refutation found. Thanks to Tanya!
% 0.56/0.64  % SZS status Theorem for theBenchmark
% 0.56/0.64  % SZS output start Proof for theBenchmark
% 0.56/0.64  fof(f165,plain,(
% 0.56/0.64    $false),
% 0.56/0.64    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f78,f85,f103,f115,f133,f159,f163])).
% 0.56/0.64  fof(f163,plain,(
% 0.56/0.64    ~spl5_1 | ~spl5_3 | ~spl5_14),
% 0.56/0.64    inference(avatar_contradiction_clause,[],[f161])).
% 0.56/0.64  fof(f161,plain,(
% 0.56/0.64    $false | (~spl5_1 | ~spl5_3 | ~spl5_14)),
% 0.56/0.64    inference(unit_resulting_resolution,[],[f54,f44,f158,f38])).
% 0.56/0.64  fof(f38,plain,(
% 0.56/0.64    ( ! [X2,X1] : (~sP3(X2) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X1)) )),
% 0.56/0.64    inference(general_splitting,[],[f33,f37_D])).
% 0.56/0.64  fof(f37,plain,(
% 0.56/0.64    ( ! [X2,X0] : (v4_relat_1(k7_relat_1(X2,X0),X0) | sP3(X2)) )),
% 0.56/0.64    inference(cnf_transformation,[],[f37_D])).
% 0.56/0.64  fof(f37_D,plain,(
% 0.56/0.64    ( ! [X2] : (( ! [X0] : v4_relat_1(k7_relat_1(X2,X0),X0) ) <=> ~sP3(X2)) )),
% 0.56/0.64    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.56/0.64  fof(f33,plain,(
% 0.56/0.64    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.56/0.64    inference(cnf_transformation,[],[f16])).
% 0.56/0.64  fof(f16,plain,(
% 0.56/0.64    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.56/0.64    inference(flattening,[],[f15])).
% 0.56/0.64  fof(f15,plain,(
% 0.56/0.64    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.56/0.64    inference(ennf_transformation,[],[f2])).
% 0.56/0.64  fof(f2,axiom,(
% 0.56/0.64    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.56/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.56/0.64  fof(f158,plain,(
% 0.56/0.64    sP3(sK2) | ~spl5_14),
% 0.56/0.64    inference(avatar_component_clause,[],[f156])).
% 0.56/0.64  fof(f156,plain,(
% 0.56/0.64    spl5_14 <=> sP3(sK2)),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.56/0.64  fof(f44,plain,(
% 0.56/0.64    v1_relat_1(sK2) | ~spl5_1),
% 0.56/0.64    inference(avatar_component_clause,[],[f42])).
% 0.56/0.64  fof(f42,plain,(
% 0.56/0.64    spl5_1 <=> v1_relat_1(sK2)),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.56/0.64  fof(f54,plain,(
% 0.56/0.64    v4_relat_1(sK2,sK0) | ~spl5_3),
% 0.56/0.64    inference(avatar_component_clause,[],[f52])).
% 0.56/0.64  fof(f52,plain,(
% 0.56/0.64    spl5_3 <=> v4_relat_1(sK2,sK0)),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.56/0.64  fof(f159,plain,(
% 0.56/0.64    spl5_14 | spl5_4 | ~spl5_12),
% 0.56/0.64    inference(avatar_split_clause,[],[f150,f130,f57,f156])).
% 0.56/0.64  fof(f57,plain,(
% 0.56/0.64    spl5_4 <=> v4_relat_1(sK2,sK1)),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.56/0.64  fof(f130,plain,(
% 0.56/0.64    spl5_12 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.56/0.64  fof(f150,plain,(
% 0.56/0.64    sP3(sK2) | (spl5_4 | ~spl5_12)),
% 0.56/0.64    inference(subsumption_resolution,[],[f144,f59])).
% 0.56/0.64  fof(f59,plain,(
% 0.56/0.64    ~v4_relat_1(sK2,sK1) | spl5_4),
% 0.56/0.64    inference(avatar_component_clause,[],[f57])).
% 0.56/0.64  fof(f144,plain,(
% 0.56/0.64    v4_relat_1(sK2,sK1) | sP3(sK2) | ~spl5_12),
% 0.56/0.64    inference(superposition,[],[f37,f132])).
% 0.56/0.64  fof(f132,plain,(
% 0.56/0.64    sK2 = k7_relat_1(sK2,sK1) | ~spl5_12),
% 0.56/0.64    inference(avatar_component_clause,[],[f130])).
% 0.56/0.64  fof(f133,plain,(
% 0.56/0.64    spl5_12 | ~spl5_1 | ~spl5_10),
% 0.56/0.64    inference(avatar_split_clause,[],[f122,f112,f42,f130])).
% 0.56/0.64  fof(f112,plain,(
% 0.56/0.64    spl5_10 <=> r1_tarski(sK2,k7_relat_1(sK2,sK1))),
% 0.56/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.56/0.64  fof(f122,plain,(
% 0.56/0.64    sK2 = k7_relat_1(sK2,sK1) | (~spl5_1 | ~spl5_10)),
% 0.56/0.64    inference(subsumption_resolution,[],[f120,f44])).
% 0.56/0.64  fof(f120,plain,(
% 0.56/0.64    sK2 = k7_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl5_10),
% 0.56/0.64    inference(resolution,[],[f114,f63])).
% 0.56/0.64  fof(f63,plain,(
% 0.56/0.64    ( ! [X2,X1] : (~r1_tarski(X1,k7_relat_1(X1,X2)) | k7_relat_1(X1,X2) = X1 | ~v1_relat_1(X1)) )),
% 0.56/0.64    inference(resolution,[],[f30,f26])).
% 0.56/0.64  fof(f26,plain,(
% 0.56/0.64    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.56/0.64    inference(cnf_transformation,[],[f10])).
% 0.56/0.64  fof(f10,plain,(
% 0.56/0.64    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.56/0.64    inference(ennf_transformation,[],[f5])).
% 0.56/0.64  fof(f5,axiom,(
% 0.56/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.56/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.56/0.64  fof(f30,plain,(
% 0.56/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.56/0.64    inference(cnf_transformation,[],[f21])).
% 0.56/0.64  fof(f21,plain,(
% 0.56/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.64    inference(flattening,[],[f20])).
% 1.11/0.64  fof(f20,plain,(
% 1.11/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.11/0.64    inference(nnf_transformation,[],[f1])).
% 1.11/0.64  fof(f1,axiom,(
% 1.11/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.11/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.11/0.64  fof(f114,plain,(
% 1.11/0.64    r1_tarski(sK2,k7_relat_1(sK2,sK1)) | ~spl5_10),
% 1.11/0.64    inference(avatar_component_clause,[],[f112])).
% 1.11/0.64  fof(f115,plain,(
% 1.11/0.64    spl5_10 | ~spl5_2 | ~spl5_9),
% 1.11/0.64    inference(avatar_split_clause,[],[f106,f101,f47,f112])).
% 1.11/0.64  fof(f47,plain,(
% 1.11/0.64    spl5_2 <=> r1_tarski(sK0,sK1)),
% 1.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.11/0.64  fof(f101,plain,(
% 1.11/0.64    spl5_9 <=> ! [X0] : (r1_tarski(sK2,k7_relat_1(sK2,X0)) | ~r1_tarski(sK0,X0))),
% 1.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.11/0.64  fof(f106,plain,(
% 1.11/0.64    r1_tarski(sK2,k7_relat_1(sK2,sK1)) | (~spl5_2 | ~spl5_9)),
% 1.11/0.64    inference(resolution,[],[f102,f49])).
% 1.11/0.64  fof(f49,plain,(
% 1.11/0.64    r1_tarski(sK0,sK1) | ~spl5_2),
% 1.11/0.64    inference(avatar_component_clause,[],[f47])).
% 1.11/0.64  fof(f102,plain,(
% 1.11/0.64    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK2,k7_relat_1(sK2,X0))) ) | ~spl5_9),
% 1.11/0.64    inference(avatar_component_clause,[],[f101])).
% 1.11/0.64  fof(f103,plain,(
% 1.11/0.64    spl5_9 | ~spl5_1 | ~spl5_8),
% 1.11/0.64    inference(avatar_split_clause,[],[f97,f82,f42,f101])).
% 1.11/0.64  fof(f82,plain,(
% 1.11/0.64    spl5_8 <=> sK2 = k7_relat_1(sK2,sK0)),
% 1.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.11/0.64  fof(f97,plain,(
% 1.11/0.64    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(sK2,X0)) | ~r1_tarski(sK0,X0)) ) | (~spl5_1 | ~spl5_8)),
% 1.11/0.64    inference(subsumption_resolution,[],[f90,f44])).
% 1.11/0.64  fof(f90,plain,(
% 1.11/0.64    ( ! [X0] : (r1_tarski(sK2,k7_relat_1(sK2,X0)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | ~spl5_8),
% 1.11/0.64    inference(superposition,[],[f31,f84])).
% 1.11/0.64  fof(f84,plain,(
% 1.11/0.64    sK2 = k7_relat_1(sK2,sK0) | ~spl5_8),
% 1.11/0.64    inference(avatar_component_clause,[],[f82])).
% 1.11/0.64  fof(f31,plain,(
% 1.11/0.64    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.11/0.64    inference(cnf_transformation,[],[f14])).
% 1.11/0.64  fof(f14,plain,(
% 1.11/0.64    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.11/0.64    inference(flattening,[],[f13])).
% 1.11/0.64  fof(f13,plain,(
% 1.11/0.64    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.11/0.64    inference(ennf_transformation,[],[f3])).
% 1.11/0.64  fof(f3,axiom,(
% 1.11/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 1.11/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).
% 1.11/0.64  fof(f85,plain,(
% 1.11/0.64    spl5_8 | ~spl5_3 | ~spl5_7),
% 1.11/0.64    inference(avatar_split_clause,[],[f80,f76,f52,f82])).
% 1.11/0.64  fof(f76,plain,(
% 1.11/0.64    spl5_7 <=> ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0))),
% 1.11/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.11/0.64  fof(f80,plain,(
% 1.11/0.64    sK2 = k7_relat_1(sK2,sK0) | (~spl5_3 | ~spl5_7)),
% 1.11/0.64    inference(resolution,[],[f77,f54])).
% 1.11/0.64  fof(f77,plain,(
% 1.11/0.64    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl5_7),
% 1.11/0.64    inference(avatar_component_clause,[],[f76])).
% 1.11/0.64  fof(f78,plain,(
% 1.11/0.64    spl5_7 | ~spl5_1),
% 1.11/0.64    inference(avatar_split_clause,[],[f73,f42,f76])).
% 1.11/0.64  fof(f73,plain,(
% 1.11/0.64    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl5_1),
% 1.11/0.64    inference(resolution,[],[f27,f44])).
% 1.11/0.64  fof(f27,plain,(
% 1.11/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.11/0.64    inference(cnf_transformation,[],[f12])).
% 1.11/0.64  fof(f12,plain,(
% 1.11/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.11/0.64    inference(flattening,[],[f11])).
% 1.11/0.64  fof(f11,plain,(
% 1.11/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.11/0.64    inference(ennf_transformation,[],[f4])).
% 1.11/0.64  fof(f4,axiom,(
% 1.11/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.11/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.11/0.64  fof(f60,plain,(
% 1.11/0.64    ~spl5_4),
% 1.11/0.64    inference(avatar_split_clause,[],[f25,f57])).
% 1.11/0.64  fof(f25,plain,(
% 1.11/0.64    ~v4_relat_1(sK2,sK1)),
% 1.11/0.64    inference(cnf_transformation,[],[f19])).
% 1.11/0.64  fof(f19,plain,(
% 1.11/0.64    (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 1.11/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17])).
% 1.11/0.64  fof(f17,plain,(
% 1.11/0.64    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 1.11/0.64    introduced(choice_axiom,[])).
% 1.11/0.64  fof(f18,plain,(
% 1.11/0.64    ? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 1.11/0.64    introduced(choice_axiom,[])).
% 1.11/0.64  fof(f9,plain,(
% 1.11/0.64    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 1.11/0.64    inference(flattening,[],[f8])).
% 1.11/0.64  fof(f8,plain,(
% 1.11/0.64    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 1.11/0.64    inference(ennf_transformation,[],[f7])).
% 1.11/0.64  fof(f7,negated_conjecture,(
% 1.11/0.64    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.11/0.64    inference(negated_conjecture,[],[f6])).
% 1.11/0.64  fof(f6,conjecture,(
% 1.11/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 1.11/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 1.11/0.64  fof(f55,plain,(
% 1.11/0.64    spl5_3),
% 1.11/0.64    inference(avatar_split_clause,[],[f24,f52])).
% 1.11/0.64  fof(f24,plain,(
% 1.11/0.64    v4_relat_1(sK2,sK0)),
% 1.11/0.64    inference(cnf_transformation,[],[f19])).
% 1.11/0.64  fof(f50,plain,(
% 1.11/0.64    spl5_2),
% 1.11/0.64    inference(avatar_split_clause,[],[f22,f47])).
% 1.11/0.64  fof(f22,plain,(
% 1.11/0.64    r1_tarski(sK0,sK1)),
% 1.11/0.64    inference(cnf_transformation,[],[f19])).
% 1.11/0.64  fof(f45,plain,(
% 1.11/0.64    spl5_1),
% 1.11/0.64    inference(avatar_split_clause,[],[f23,f42])).
% 1.11/0.64  fof(f23,plain,(
% 1.11/0.64    v1_relat_1(sK2)),
% 1.11/0.64    inference(cnf_transformation,[],[f19])).
% 1.11/0.64  % SZS output end Proof for theBenchmark
% 1.11/0.64  % (27517)------------------------------
% 1.11/0.64  % (27517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.64  % (27517)Termination reason: Refutation
% 1.11/0.64  
% 1.11/0.64  % (27517)Memory used [KB]: 6140
% 1.11/0.64  % (27517)Time elapsed: 0.076 s
% 1.11/0.64  % (27517)------------------------------
% 1.11/0.64  % (27517)------------------------------
% 1.11/0.65  % (27518)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.11/0.65  % (27526)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.11/0.65  % (27530)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.11/0.66  % (27527)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.11/0.66  % (27522)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.11/0.66  % (27534)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.11/0.66  % (27380)Success in time 0.3 s
%------------------------------------------------------------------------------

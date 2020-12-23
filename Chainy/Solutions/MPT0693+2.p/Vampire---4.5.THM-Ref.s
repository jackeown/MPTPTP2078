%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0693+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 180 expanded)
%              Number of equality atoms :   41 (  58 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2920,f2925,f2935,f3092,f5030])).

fof(f5030,plain,
    ( ~ spl141_1
    | ~ spl141_2
    | spl141_15 ),
    inference(avatar_contradiction_clause,[],[f5029])).

fof(f5029,plain,
    ( $false
    | ~ spl141_1
    | ~ spl141_2
    | spl141_15 ),
    inference(subsumption_resolution,[],[f5028,f1917])).

fof(f1917,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f1007])).

fof(f1007,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f5028,plain,
    ( k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))) != k3_xboole_0(k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))),k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))))
    | ~ spl141_1
    | ~ spl141_2
    | spl141_15 ),
    inference(forward_demodulation,[],[f5023,f1915])).

fof(f1915,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f5023,plain,
    ( k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))) != k3_xboole_0(k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))),k1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0)))
    | ~ spl141_1
    | ~ spl141_2
    | spl141_15 ),
    inference(backward_demodulation,[],[f3228,f5021])).

fof(f5021,plain,
    ( ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k3_xboole_0(k2_relat_1(sK1),X0)
    | ~ spl141_1
    | ~ spl141_2 ),
    inference(forward_demodulation,[],[f4998,f3377])).

fof(f3377,plain,
    ( ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))
    | ~ spl141_1 ),
    inference(unit_resulting_resolution,[],[f2919,f1983])).

fof(f1983,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f1093])).

fof(f1093,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f770])).

fof(f770,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f2919,plain,
    ( v1_relat_1(sK1)
    | ~ spl141_1 ),
    inference(avatar_component_clause,[],[f2917])).

fof(f2917,plain,
    ( spl141_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl141_1])])).

fof(f4998,plain,
    ( ! [X0] : k3_xboole_0(k2_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)))
    | ~ spl141_1
    | ~ spl141_2 ),
    inference(unit_resulting_resolution,[],[f2919,f2924,f1916,f1971])).

fof(f1971,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1079])).

fof(f1079,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1078])).

fof(f1078,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f947])).

fof(f947,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1916,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2924,plain,
    ( v1_funct_1(sK1)
    | ~ spl141_2 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2922,plain,
    ( spl141_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl141_2])])).

fof(f3228,plain,
    ( k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))) != k3_xboole_0(k1_tarski(k3_xboole_0(sK0,k2_relat_1(sK1))),k1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0))))
    | spl141_15 ),
    inference(unit_resulting_resolution,[],[f3091,f1905])).

fof(f1905,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1028])).

% (31790)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
fof(f1028,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f374])).

fof(f374,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f3091,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | spl141_15 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f3089,plain,
    ( spl141_15
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl141_15])])).

fof(f3092,plain,
    ( ~ spl141_15
    | ~ spl141_1
    | spl141_4 ),
    inference(avatar_split_clause,[],[f3076,f2932,f2917,f3089])).

fof(f2932,plain,
    ( spl141_4
  <=> k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl141_4])])).

fof(f3076,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl141_1
    | spl141_4 ),
    inference(backward_demodulation,[],[f2934,f3074])).

fof(f3074,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)
    | ~ spl141_1 ),
    inference(unit_resulting_resolution,[],[f2919,f1958])).

fof(f1958,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f1066])).

fof(f1066,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f748])).

fof(f748,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f2934,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    | spl141_4 ),
    inference(avatar_component_clause,[],[f2932])).

fof(f2935,plain,(
    ~ spl141_4 ),
    inference(avatar_split_clause,[],[f1881,f2932])).

fof(f1881,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f1557])).

fof(f1557,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1015,f1556])).

fof(f1556,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != k3_xboole_0(sK0,k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1015,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1014])).

fof(f1014,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f949])).

fof(f949,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f948])).

fof(f948,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f2925,plain,(
    spl141_2 ),
    inference(avatar_split_clause,[],[f1880,f2922])).

fof(f1880,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1557])).

fof(f2920,plain,(
    spl141_1 ),
    inference(avatar_split_clause,[],[f1879,f2917])).

fof(f1879,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1557])).
%------------------------------------------------------------------------------

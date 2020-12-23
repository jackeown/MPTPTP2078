%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0588+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   56 (  90 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 172 expanded)
%              Number of equality atoms :   48 (  66 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3322,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2050,f2060,f3278])).

fof(f3278,plain,
    ( ~ spl91_1
    | spl91_3 ),
    inference(avatar_contradiction_clause,[],[f3277])).

fof(f3277,plain,
    ( $false
    | ~ spl91_1
    | spl91_3 ),
    inference(subsumption_resolution,[],[f3274,f1388])).

fof(f1388,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f849])).

fof(f849,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f3274,plain,
    ( k1_tarski(k7_relat_1(sK1,sK0)) != k3_xboole_0(k1_tarski(k7_relat_1(sK1,sK0)),k1_tarski(k7_relat_1(sK1,sK0)))
    | ~ spl91_1
    | spl91_3 ),
    inference(backward_demodulation,[],[f2323,f3272])).

fof(f3272,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(X0,k1_relat_1(sK1)))
    | ~ spl91_1 ),
    inference(forward_demodulation,[],[f3271,f2344])).

fof(f2344,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl91_1 ),
    inference(backward_demodulation,[],[f2191,f2341])).

fof(f2341,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl91_1 ),
    inference(unit_resulting_resolution,[],[f2049,f1415])).

fof(f1415,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f905])).

fof(f905,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f839])).

fof(f839,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f2049,plain,
    ( v1_relat_1(sK1)
    | ~ spl91_1 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f2047,plain,
    ( spl91_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_1])])).

fof(f2191,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl91_1 ),
    inference(unit_resulting_resolution,[],[f2089,f1432])).

fof(f1432,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f919])).

fof(f919,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f847])).

fof(f847,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f2089,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl91_1 ),
    inference(unit_resulting_resolution,[],[f2049,f1421])).

fof(f1421,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f911])).

fof(f911,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f661])).

fof(f661,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f3271,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(X0,k1_relat_1(sK1)))
    | ~ spl91_1 ),
    inference(forward_demodulation,[],[f3270,f2690])).

fof(f2690,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1))
    | ~ spl91_1 ),
    inference(unit_resulting_resolution,[],[f2049,f1403])).

fof(f1403,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f890])).

fof(f890,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f691])).

fof(f691,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f3270,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl91_1 ),
    inference(forward_demodulation,[],[f3269,f2292])).

fof(f2292,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1374,f1388])).

fof(f1374,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f3269,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),X0)))
    | ~ spl91_1 ),
    inference(forward_demodulation,[],[f3268,f2341])).

fof(f3268,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))))
    | ~ spl91_1 ),
    inference(forward_demodulation,[],[f3247,f2341])).

fof(f3247,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(sK1)) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))))
    | ~ spl91_1 ),
    inference(unit_resulting_resolution,[],[f2089,f2049,f1431])).

fof(f1431,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f918])).

fof(f918,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f777])).

fof(f777,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f2323,plain,
    ( k1_tarski(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))) != k3_xboole_0(k1_tarski(k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))),k1_tarski(k7_relat_1(sK1,sK0)))
    | spl91_3 ),
    inference(unit_resulting_resolution,[],[f2059,f1376])).

fof(f1376,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f867])).

fof(f867,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f374])).

fof(f374,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f2059,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1)))
    | spl91_3 ),
    inference(avatar_component_clause,[],[f2057])).

fof(f2057,plain,
    ( spl91_3
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl91_3])])).

fof(f2060,plain,(
    ~ spl91_3 ),
    inference(avatar_split_clause,[],[f2016,f2057])).

fof(f2016,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f1352,f1386])).

fof(f1386,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1352,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f1149])).

fof(f1149,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f854,f1148])).

fof(f1148,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f854,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f782])).

fof(f782,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f781])).

fof(f781,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f2050,plain,(
    spl91_1 ),
    inference(avatar_split_clause,[],[f1351,f2047])).

fof(f1351,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1149])).
%------------------------------------------------------------------------------

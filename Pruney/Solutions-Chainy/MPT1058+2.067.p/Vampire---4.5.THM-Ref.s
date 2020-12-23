%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 147 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  182 ( 327 expanded)
%              Number of equality atoms :   52 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f114,f353])).

fof(f353,plain,
    ( ~ spl3_2
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl3_2
    | spl3_6 ),
    inference(subsumption_resolution,[],[f350,f55])).

fof(f55,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f350,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | spl3_6 ),
    inference(trivial_inequality_removal,[],[f342])).

fof(f342,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2)
    | ~ r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | spl3_6 ),
    inference(superposition,[],[f113,f288])).

fof(f288,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X6,X5) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f287,f149])).

fof(f149,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f148,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f148,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f142,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f128,f35])).

fof(f35,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f36,f38])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f287,plain,(
    ! [X6,X5] :
      ( k10_relat_1(k6_relat_1(X5),X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(subsumption_resolution,[],[f286,f139])).

fof(f139,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f138,f38])).

fof(f138,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),X0) ),
    inference(forward_demodulation,[],[f137,f38])).

fof(f137,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f125,f35])).

fof(f125,plain,(
    ! [X8,X7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k1_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X8,X7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k1_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f286,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k3_xboole_0(X6,X5),X5)
      | k10_relat_1(k6_relat_1(X5),X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f285,f149])).

fof(f285,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k10_relat_1(k6_relat_1(X5),X6),X5)
      | k10_relat_1(k6_relat_1(X5),X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(subsumption_resolution,[],[f270,f42])).

fof(f270,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k10_relat_1(k6_relat_1(X5),X6),X5)
      | ~ v1_relat_1(k6_relat_1(X5))
      | k10_relat_1(k6_relat_1(X5),X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f89,f82])).

fof(f82,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f81,f38])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f37,f39])).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f113,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_6
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f109,f58,f48,f111])).

fof(f48,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f108,f60])).

fof(f60,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f108,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f50,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f50,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24280)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (24278)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (24279)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (24275)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (24282)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (24276)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (24303)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (24296)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (24288)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (24303)Refutation not found, incomplete strategy% (24303)------------------------------
% 0.20/0.52  % (24303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24303)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24303)Memory used [KB]: 10746
% 0.20/0.52  % (24303)Time elapsed: 0.110 s
% 0.20/0.52  % (24303)------------------------------
% 0.20/0.52  % (24303)------------------------------
% 0.20/0.52  % (24289)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (24274)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (24277)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (24293)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (24287)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (24283)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (24296)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (24300)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (24275)Refutation not found, incomplete strategy% (24275)------------------------------
% 0.20/0.53  % (24275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24275)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24275)Memory used [KB]: 1663
% 0.20/0.53  % (24275)Time elapsed: 0.117 s
% 0.20/0.53  % (24275)------------------------------
% 0.20/0.53  % (24275)------------------------------
% 0.20/0.53  % (24295)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (24290)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (24292)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (24284)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.53  % (24301)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.53  % (24281)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.36/0.53  % (24302)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.54  % (24298)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.54  % (24294)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.54  % (24297)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.54  % (24293)Refutation not found, incomplete strategy% (24293)------------------------------
% 1.36/0.54  % (24293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (24304)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (24284)Refutation not found, incomplete strategy% (24284)------------------------------
% 1.36/0.54  % (24284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (24284)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (24284)Memory used [KB]: 10746
% 1.36/0.54  % (24284)Time elapsed: 0.135 s
% 1.36/0.54  % (24284)------------------------------
% 1.36/0.54  % (24284)------------------------------
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f354,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f51,f56,f61,f114,f353])).
% 1.36/0.54  fof(f353,plain,(
% 1.36/0.54    ~spl3_2 | spl3_6),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f352])).
% 1.36/0.54  fof(f352,plain,(
% 1.36/0.54    $false | (~spl3_2 | spl3_6)),
% 1.36/0.54    inference(subsumption_resolution,[],[f350,f55])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f53])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.36/0.54  fof(f350,plain,(
% 1.36/0.54    ~r1_tarski(k10_relat_1(sK0,sK2),sK1) | spl3_6),
% 1.36/0.54    inference(trivial_inequality_removal,[],[f342])).
% 1.36/0.54  fof(f342,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) | ~r1_tarski(k10_relat_1(sK0,sK2),sK1) | spl3_6),
% 1.36/0.54    inference(superposition,[],[f113,f288])).
% 1.36/0.54  fof(f288,plain,(
% 1.36/0.54    ( ! [X6,X5] : (k3_xboole_0(X6,X5) = X5 | ~r1_tarski(X5,X6)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f287,f149])).
% 1.36/0.54  fof(f149,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f148,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.54  fof(f148,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f142,f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.36/0.54    inference(pure_predicate_removal,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.36/0.54  fof(f142,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(superposition,[],[f128,f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.36/0.54  fof(f128,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f115,f42])).
% 1.36/0.54  fof(f115,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(superposition,[],[f36,f38])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 1.36/0.54  fof(f287,plain,(
% 1.36/0.54    ( ! [X6,X5] : (k10_relat_1(k6_relat_1(X5),X6) = X5 | ~r1_tarski(X5,X6)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f286,f139])).
% 1.36/0.54  fof(f139,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f138,f38])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),X0)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f137,f38])).
% 1.36/0.54  fof(f137,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f136,f42])).
% 1.36/0.54  fof(f136,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f134,f42])).
% 1.36/0.54  fof(f134,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.36/0.54    inference(superposition,[],[f125,f35])).
% 1.36/0.54  fof(f125,plain,(
% 1.36/0.54    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k1_relat_1(X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X8)) )),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f121])).
% 1.36/0.54  fof(f121,plain,(
% 1.36/0.54    ( ! [X8,X7] : (r1_tarski(k1_relat_1(k5_relat_1(X7,X8)),k1_relat_1(X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X8) | ~v1_relat_1(X7)) )),
% 1.36/0.54    inference(superposition,[],[f41,f36])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.36/0.54  fof(f286,plain,(
% 1.36/0.54    ( ! [X6,X5] : (~r1_tarski(k3_xboole_0(X6,X5),X5) | k10_relat_1(k6_relat_1(X5),X6) = X5 | ~r1_tarski(X5,X6)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f285,f149])).
% 1.36/0.54  fof(f285,plain,(
% 1.36/0.54    ( ! [X6,X5] : (~r1_tarski(k10_relat_1(k6_relat_1(X5),X6),X5) | k10_relat_1(k6_relat_1(X5),X6) = X5 | ~r1_tarski(X5,X6)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f270,f42])).
% 1.36/0.54  fof(f270,plain,(
% 1.36/0.54    ( ! [X6,X5] : (~r1_tarski(k10_relat_1(k6_relat_1(X5),X6),X5) | ~v1_relat_1(k6_relat_1(X5)) | k10_relat_1(k6_relat_1(X5),X6) = X5 | ~r1_tarski(X5,X6)) )),
% 1.36/0.54    inference(superposition,[],[f89,f82])).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.36/0.54    inference(forward_demodulation,[],[f81,f38])).
% 1.36/0.54  fof(f81,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f77,f42])).
% 1.36/0.54  fof(f77,plain,(
% 1.36/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.54    inference(superposition,[],[f37,f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | k10_relat_1(X2,X0) = k10_relat_1(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(resolution,[],[f40,f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(flattening,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(nnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(flattening,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 1.36/0.54  fof(f113,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f111])).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    spl3_6 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.36/0.54  fof(f114,plain,(
% 1.36/0.54    ~spl3_6 | spl3_1 | ~spl3_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f109,f58,f48,f111])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    spl3_3 <=> v1_relat_1(sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_3)),
% 1.36/0.54    inference(subsumption_resolution,[],[f108,f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    v1_relat_1(sK0) | ~spl3_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f58])).
% 1.36/0.54  fof(f108,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.36/0.54    inference(superposition,[],[f50,f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.36/0.54    inference(ennf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f48])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    spl3_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f28,f58])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    v1_relat_1(sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f24,f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.36/0.54    inference(pure_predicate_removal,[],[f13])).
% 1.36/0.54  fof(f13,negated_conjecture,(
% 1.36/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.36/0.54    inference(negated_conjecture,[],[f12])).
% 1.36/0.54  fof(f12,conjecture,(
% 1.36/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    spl3_2),
% 1.36/0.54    inference(avatar_split_clause,[],[f29,f53])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ~spl3_1),
% 1.36/0.54    inference(avatar_split_clause,[],[f30,f48])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (24296)------------------------------
% 1.36/0.54  % (24296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (24296)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (24296)Memory used [KB]: 6396
% 1.36/0.54  % (24296)Time elapsed: 0.115 s
% 1.36/0.54  % (24296)------------------------------
% 1.36/0.54  % (24296)------------------------------
% 1.36/0.54  % (24293)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (24293)Memory used [KB]: 1791
% 1.36/0.54  % (24293)Time elapsed: 0.126 s
% 1.36/0.54  % (24293)------------------------------
% 1.36/0.54  % (24293)------------------------------
% 1.36/0.54  % (24271)Success in time 0.183 s
%------------------------------------------------------------------------------

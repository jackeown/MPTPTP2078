%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 708 expanded)
%              Number of leaves         :   20 ( 219 expanded)
%              Depth                    :   22
%              Number of atoms          :  305 (2344 expanded)
%              Number of equality atoms :   55 ( 193 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f122,f195,f226,f238,f268,f329])).

fof(f329,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f327,f50])).

fof(f50,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(f327,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f319,f142])).

fof(f142,plain,
    ( ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f138,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(resolution,[],[f134,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f134,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_6 ),
    inference(resolution,[],[f124,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f124,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f105,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f105,plain,(
    ! [X0] : r1_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f86,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f85,f47])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f76,f48])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f53,f75])).

fof(f75,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f49,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f138,plain,
    ( ! [X1] : k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = X1
    | ~ spl2_6 ),
    inference(resolution,[],[f134,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f319,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(superposition,[],[f68,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f297,f221])).

fof(f221,plain,
    ( v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl2_10
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f297,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(superposition,[],[f294,f115])).

fof(f294,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_relat_1(X2)
        | k1_xboole_0 = X2
        | ~ v1_relat_1(X2) )
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f285,f103])).

fof(f103,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f285,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | k1_xboole_0 != k1_relat_1(X2)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X2) )
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 != k1_relat_1(X2)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X2) )
    | ~ spl2_15 ),
    inference(superposition,[],[f52,f257])).

fof(f257,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl2_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | X0 = X1
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k1_relat_1(X1)
          | k1_xboole_0 != k1_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | k1_xboole_0 != k1_relat_1(X1)
          | k1_xboole_0 != k1_relat_1(X0)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f268,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f263,f224,f113,f101,f255])).

fof(f224,plain,
    ( spl2_11
  <=> ! [X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f263,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f249,f62])).

fof(f249,plain,
    ( ! [X0] : r1_xboole_0(k1_relat_1(k1_xboole_0),X0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f246,f142])).

fof(f246,plain,
    ( ! [X0] : r1_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(resolution,[],[f245,f65])).

fof(f245,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f242,f103])).

fof(f242,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f225,f144])).

fof(f144,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f136,f142])).

fof(f136,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0))
    | ~ spl2_6 ),
    inference(resolution,[],[f124,f57])).

fof(f225,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f224])).

fof(f238,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f236,f47])).

fof(f236,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_10 ),
    inference(resolution,[],[f222,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f222,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f220])).

fof(f226,plain,
    ( ~ spl2_10
    | spl2_11
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f218,f113,f224,f220])).

fof(f218,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0)
        | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f211,f141])).

fof(f141,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f139,f140])).

fof(f139,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_6 ),
    inference(resolution,[],[f134,f57])).

fof(f211,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_relat_1(X0),k1_xboole_0))
        | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(superposition,[],[f53,f115])).

fof(f195,plain,
    ( spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f185,f47])).

fof(f185,plain,
    ( ! [X1] : ~ v1_relat_1(X1)
    | spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f178,f102])).

fof(f102,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f178,plain,
    ( ! [X1] :
        ( v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(superposition,[],[f54,f141])).

fof(f122,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f117,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f111,f53])).

fof(f111,plain,
    ( ! [X2] : ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_5
  <=> ! [X2] : ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f116,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f108,f113,f110])).

fof(f108,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2) ) ),
    inference(subsumption_resolution,[],[f107,f63])).

fof(f63,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f107,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2) ) ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:11:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (5338)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (5332)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (5333)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (5331)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (5330)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (5349)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (5347)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (5342)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (5341)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (5350)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (5334)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (5343)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (5351)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (5339)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (5334)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f116,f122,f195,f226,f238,f268,f329])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    ~spl2_4 | ~spl2_6 | ~spl2_10 | ~spl2_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f328])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    $false | (~spl2_4 | ~spl2_6 | ~spl2_10 | ~spl2_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f327,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f22])).
% 0.22/0.53  fof(f22,conjecture,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    r1_xboole_0(sK0,sK1) | (~spl2_4 | ~spl2_6 | ~spl2_10 | ~spl2_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f319,f142])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl2_6),
% 0.22/0.53    inference(backward_demodulation,[],[f138,f140])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_6),
% 0.22/0.53    inference(resolution,[],[f134,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ) | ~spl2_6),
% 0.22/0.53    inference(resolution,[],[f124,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) ) | ~spl2_6),
% 0.22/0.53    inference(backward_demodulation,[],[f105,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl2_6 <=> k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.53    inference(resolution,[],[f86,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f85,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f76,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.22/0.53    inference(superposition,[],[f53,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.53    inference(resolution,[],[f49,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = X1) ) | ~spl2_6),
% 0.22/0.53    inference(resolution,[],[f134,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) | (~spl2_4 | ~spl2_6 | ~spl2_10 | ~spl2_15)),
% 0.22/0.53    inference(superposition,[],[f68,f298])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl2_4 | ~spl2_6 | ~spl2_10 | ~spl2_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f297,f221])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    v1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f220])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    spl2_10 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_15)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f295])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_15)),
% 0.22/0.53    inference(superposition,[],[f294,f115])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 != k1_relat_1(X2) | k1_xboole_0 = X2 | ~v1_relat_1(X2)) ) | (~spl2_4 | ~spl2_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f285,f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    v1_relat_1(k1_xboole_0) | ~spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = X2 | k1_xboole_0 != k1_relat_1(X2) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X2)) ) | ~spl2_15),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f284])).
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X2 | k1_xboole_0 != k1_relat_1(X2) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X2)) ) | ~spl2_15),
% 0.22/0.53    inference(superposition,[],[f52,f257])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f255])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    spl2_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | X0 = X1 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (X0 = X1 | k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((X0 = X1 | (k1_xboole_0 != k1_relat_1(X1) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    spl2_15 | ~spl2_4 | ~spl2_6 | ~spl2_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f263,f224,f113,f101,f255])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    spl2_11 <=> ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.22/0.53    inference(resolution,[],[f249,f62])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) ) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f246,f142])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(X0,k1_xboole_0))) ) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.22/0.53    inference(resolution,[],[f245,f65])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f242,f103])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl2_6 | ~spl2_11)),
% 0.22/0.53    inference(superposition,[],[f225,f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl2_6),
% 0.22/0.53    inference(backward_demodulation,[],[f136,f142])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0))) ) | ~spl2_6),
% 0.22/0.53    inference(resolution,[],[f124,f57])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f224])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    spl2_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    $false | spl2_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f236,f47])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ~v1_relat_1(sK0) | spl2_10),
% 0.22/0.53    inference(resolution,[],[f222,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f220])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ~spl2_10 | spl2_11 | ~spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f218,f113,f224,f220])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k1_xboole_0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.22/0.53    inference(forward_demodulation,[],[f211,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | ~spl2_6),
% 0.22/0.53    inference(backward_demodulation,[],[f139,f140])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ) | ~spl2_6),
% 0.22/0.53    inference(resolution,[],[f134,f57])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_relat_1(X0),k1_xboole_0)) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.22/0.53    inference(superposition,[],[f53,f115])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl2_4 | ~spl2_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    $false | (spl2_4 | ~spl2_6)),
% 0.22/0.53    inference(resolution,[],[f185,f47])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ( ! [X1] : (~v1_relat_1(X1)) ) | (spl2_4 | ~spl2_6)),
% 0.22/0.53    inference(subsumption_resolution,[],[f178,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ~v1_relat_1(k1_xboole_0) | spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.22/0.53    inference(superposition,[],[f54,f141])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~spl2_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    $false | ~spl2_5),
% 0.22/0.53    inference(subsumption_resolution,[],[f120,f47])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ~v1_relat_1(sK0) | ~spl2_5),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f48])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl2_5),
% 0.22/0.53    inference(resolution,[],[f111,f53])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2)) ) | ~spl2_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl2_5 <=> ! [X2] : ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl2_5 | spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f108,f113,f110])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X2] : (k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X2] : (~r1_xboole_0(X2,k1_xboole_0) | k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),X2)) )),
% 0.22/0.53    inference(resolution,[],[f86,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (5334)------------------------------
% 0.22/0.53  % (5334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5334)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (5334)Memory used [KB]: 10746
% 0.22/0.53  % (5334)Time elapsed: 0.107 s
% 0.22/0.53  % (5334)------------------------------
% 0.22/0.53  % (5334)------------------------------
% 0.22/0.53  % (5327)Success in time 0.164 s
%------------------------------------------------------------------------------

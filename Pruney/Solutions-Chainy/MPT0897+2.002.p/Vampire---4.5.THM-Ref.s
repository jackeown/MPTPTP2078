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
% DateTime   : Thu Dec  3 12:59:13 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 540 expanded)
%              Number of leaves         :   25 ( 165 expanded)
%              Depth                    :   15
%              Number of atoms          :  361 (1464 expanded)
%              Number of equality atoms :   79 ( 565 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f734,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f218,f252,f257,f441,f459,f491,f510,f560,f666,f672,f675,f729,f732])).

fof(f732,plain,
    ( spl9_13
    | ~ spl9_32
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | spl9_13
    | ~ spl9_32
    | spl9_34 ),
    inference(subsumption_resolution,[],[f730,f144])).

fof(f144,plain,
    ( ~ v1_xboole_0(sK4)
    | spl9_13 ),
    inference(resolution,[],[f134,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f134,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | spl9_13 ),
    inference(resolution,[],[f131,f36])).

fof(f131,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_13
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

% (5679)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f730,plain,
    ( v1_xboole_0(sK4)
    | ~ spl9_32
    | spl9_34 ),
    inference(subsumption_resolution,[],[f725,f509])).

fof(f509,plain,
    ( ~ r1_tarski(sK5,sK1)
    | spl9_34 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl9_34
  <=> r1_tarski(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f725,plain,
    ( r1_tarski(sK5,sK1)
    | v1_xboole_0(sK4)
    | ~ spl9_32 ),
    inference(resolution,[],[f495,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f495,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl9_32
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f729,plain,
    ( spl9_6
    | spl9_13
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | spl9_6
    | spl9_13
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f727,f143])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK5)
    | spl9_13 ),
    inference(resolution,[],[f134,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f727,plain,
    ( v1_xboole_0(sK5)
    | spl9_6
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f724,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK4,sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_6
  <=> r1_tarski(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f724,plain,
    ( r1_tarski(sK4,sK0)
    | v1_xboole_0(sK5)
    | ~ spl9_32 ),
    inference(resolution,[],[f495,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f675,plain,
    ( spl9_13
    | ~ spl9_28
    | spl9_30 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | spl9_13
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f673,f134])).

fof(f673,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | ~ spl9_28
    | spl9_30 ),
    inference(subsumption_resolution,[],[f668,f440])).

fof(f440,plain,
    ( ~ r1_tarski(sK6,sK2)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl9_30
  <=> r1_tarski(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f668,plain,
    ( r1_tarski(sK6,sK2)
    | v1_xboole_0(k2_zfmisc_1(sK4,sK5))
    | ~ spl9_28 ),
    inference(resolution,[],[f429,f30])).

fof(f429,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl9_28
  <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f672,plain,
    ( spl9_13
    | ~ spl9_28
    | spl9_32 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | spl9_13
    | ~ spl9_28
    | spl9_32 ),
    inference(subsumption_resolution,[],[f670,f133])).

fof(f133,plain,
    ( ~ v1_xboole_0(sK6)
    | spl9_13 ),
    inference(resolution,[],[f131,f37])).

fof(f670,plain,
    ( v1_xboole_0(sK6)
    | ~ spl9_28
    | spl9_32 ),
    inference(subsumption_resolution,[],[f667,f496])).

fof(f496,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | spl9_32 ),
    inference(avatar_component_clause,[],[f494])).

fof(f667,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK6)
    | ~ spl9_28 ),
    inference(resolution,[],[f429,f31])).

fof(f666,plain,
    ( ~ spl9_4
    | spl9_12
    | spl9_28 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl9_4
    | spl9_12
    | spl9_28 ),
    inference(subsumption_resolution,[],[f593,f430])).

fof(f430,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl9_28 ),
    inference(avatar_component_clause,[],[f428])).

fof(f593,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl9_4
    | spl9_12 ),
    inference(forward_demodulation,[],[f592,f406])).

fof(f406,plain,
    ( ! [X16] : k1_relat_1(k2_zfmisc_1(X16,sK3)) = X16
    | spl9_12 ),
    inference(resolution,[],[f328,f270])).

fof(f270,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_12 ),
    inference(resolution,[],[f125,f37])).

fof(f125,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_12
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f328,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 ) ),
    inference(subsumption_resolution,[],[f324,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f324,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X0)),X1) ) ),
    inference(resolution,[],[f151,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f151,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f145,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f592,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)))
    | ~ spl9_4
    | spl9_12 ),
    inference(subsumption_resolution,[],[f583,f270])).

fof(f583,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)))
    | v1_xboole_0(sK3)
    | ~ spl9_4 ),
    inference(superposition,[],[f151,f562])).

fof(f562,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f46,f63])).

fof(f63,plain,
    ( sK3 = sK7
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl9_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f46,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f27,f44,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f42,f41])).

% (5680)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f41,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f27,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f560,plain,
    ( spl9_12
    | spl9_31 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | spl9_12
    | spl9_31 ),
    inference(subsumption_resolution,[],[f558,f271])).

fof(f271,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl9_12 ),
    inference(resolution,[],[f125,f36])).

fof(f558,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl9_31 ),
    inference(subsumption_resolution,[],[f554,f458])).

fof(f458,plain,
    ( ~ r1_tarski(sK3,sK7)
    | spl9_31 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl9_31
  <=> r1_tarski(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f554,plain,
    ( r1_tarski(sK3,sK7)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f140,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f140,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
      | r1_tarski(X4,sK7)
      | v1_xboole_0(X3) ) ),
    inference(superposition,[],[f30,f46])).

fof(f510,plain,
    ( ~ spl9_34
    | spl9_2
    | spl9_12 ),
    inference(avatar_split_clause,[],[f505,f124,f54,f507])).

fof(f54,plain,
    ( spl9_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f505,plain,
    ( sK1 = sK5
    | ~ r1_tarski(sK5,sK1)
    | spl9_12 ),
    inference(resolution,[],[f492,f40])).

% (5662)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f492,plain,
    ( r1_tarski(sK1,sK5)
    | spl9_12 ),
    inference(subsumption_resolution,[],[f487,f287])).

fof(f287,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_12 ),
    inference(resolution,[],[f282,f36])).

fof(f282,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl9_12 ),
    inference(resolution,[],[f271,f36])).

fof(f487,plain,
    ( r1_tarski(sK1,sK5)
    | v1_xboole_0(sK0)
    | spl9_12 ),
    inference(resolution,[],[f425,f30])).

fof(f425,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl9_12 ),
    inference(subsumption_resolution,[],[f422,f281])).

fof(f281,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_12 ),
    inference(resolution,[],[f271,f37])).

fof(f422,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | v1_xboole_0(sK2)
    | spl9_12 ),
    inference(resolution,[],[f411,f31])).

fof(f411,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl9_12 ),
    inference(backward_demodulation,[],[f117,f406])).

fof(f117,plain,(
    r1_tarski(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(superposition,[],[f35,f46])).

fof(f491,plain,
    ( spl9_5
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | spl9_5
    | spl9_12 ),
    inference(subsumption_resolution,[],[f489,f286])).

fof(f286,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_12 ),
    inference(resolution,[],[f282,f37])).

fof(f489,plain,
    ( v1_xboole_0(sK1)
    | spl9_5
    | spl9_12 ),
    inference(subsumption_resolution,[],[f486,f89])).

fof(f89,plain,
    ( ~ r1_tarski(sK0,sK4)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_5
  <=> r1_tarski(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f486,plain,
    ( r1_tarski(sK0,sK4)
    | v1_xboole_0(sK1)
    | spl9_12 ),
    inference(resolution,[],[f425,f31])).

fof(f459,plain,
    ( ~ spl9_31
    | spl9_4
    | spl9_13 ),
    inference(avatar_split_clause,[],[f454,f129,f62,f456])).

fof(f454,plain,
    ( sK3 = sK7
    | ~ r1_tarski(sK3,sK7)
    | spl9_13 ),
    inference(resolution,[],[f450,f40])).

fof(f450,plain,
    ( r1_tarski(sK7,sK3)
    | spl9_13 ),
    inference(resolution,[],[f142,f47])).

fof(f142,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X3,X4))
        | r1_tarski(sK7,X4) )
    | spl9_13 ),
    inference(subsumption_resolution,[],[f138,f131])).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X3,X4))
      | r1_tarski(sK7,X4)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ) ),
    inference(superposition,[],[f30,f46])).

fof(f441,plain,
    ( ~ spl9_30
    | spl9_3
    | spl9_12 ),
    inference(avatar_split_clause,[],[f436,f124,f58,f438])).

% (5680)Refutation not found, incomplete strategy% (5680)------------------------------
% (5680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5680)Termination reason: Refutation not found, incomplete strategy

% (5680)Memory used [KB]: 6268
% (5680)Time elapsed: 0.152 s
% (5680)------------------------------
% (5680)------------------------------
fof(f58,plain,
    ( spl9_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f436,plain,
    ( sK2 = sK6
    | ~ r1_tarski(sK6,sK2)
    | spl9_12 ),
    inference(resolution,[],[f426,f40])).

fof(f426,plain,
    ( r1_tarski(sK2,sK6)
    | spl9_12 ),
    inference(subsumption_resolution,[],[f423,f282])).

fof(f423,plain,
    ( r1_tarski(sK2,sK6)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl9_12 ),
    inference(resolution,[],[f411,f30])).

fof(f257,plain,
    ( ~ spl9_13
    | spl9_12 ),
    inference(avatar_split_clause,[],[f254,f124,f129])).

fof(f254,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(superposition,[],[f36,f46])).

fof(f252,plain,(
    ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f245,f45])).

fof(f45,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f28,f44])).

fof(f28,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f245,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl9_12 ),
    inference(resolution,[],[f126,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f126,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f124])).

% (5664)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f218,plain,
    ( ~ spl9_6
    | ~ spl9_5
    | spl9_1 ),
    inference(avatar_split_clause,[],[f216,f50,f87,f91])).

fof(f50,plain,
    ( spl9_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f216,plain,
    ( ~ r1_tarski(sK0,sK4)
    | ~ r1_tarski(sK4,sK0)
    | spl9_1 ),
    inference(extensionality_resolution,[],[f40,f52])).

fof(f52,plain,
    ( sK0 != sK4
    | spl9_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f65,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f29,f62,f58,f54,f50])).

fof(f29,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5676)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (5667)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (5667)Refutation not found, incomplete strategy% (5667)------------------------------
% 0.22/0.51  % (5667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5667)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (5667)Memory used [KB]: 1663
% 0.22/0.51  % (5667)Time elapsed: 0.060 s
% 0.22/0.51  % (5667)------------------------------
% 0.22/0.51  % (5667)------------------------------
% 0.22/0.52  % (5658)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (5659)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (5673)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (5656)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (5657)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (5669)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (5677)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (5682)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (5654)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (5654)Refutation not found, incomplete strategy% (5654)------------------------------
% 0.22/0.54  % (5654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5654)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5654)Memory used [KB]: 1663
% 0.22/0.54  % (5654)Time elapsed: 0.131 s
% 0.22/0.54  % (5654)------------------------------
% 0.22/0.54  % (5654)------------------------------
% 0.22/0.54  % (5675)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (5665)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (5672)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (5672)Refutation not found, incomplete strategy% (5672)------------------------------
% 0.22/0.55  % (5672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5672)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5672)Memory used [KB]: 1663
% 0.22/0.55  % (5672)Time elapsed: 0.138 s
% 0.22/0.55  % (5672)------------------------------
% 0.22/0.55  % (5672)------------------------------
% 0.22/0.55  % (5665)Refutation not found, incomplete strategy% (5665)------------------------------
% 0.22/0.55  % (5665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5665)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5665)Memory used [KB]: 10618
% 0.22/0.55  % (5665)Time elapsed: 0.139 s
% 0.22/0.55  % (5665)------------------------------
% 0.22/0.55  % (5665)------------------------------
% 0.22/0.55  % (5655)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.55  % (5674)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % (5663)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (5653)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.56  % (5666)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (5660)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.56  % (5671)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.56  % (5659)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % (5681)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f734,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(avatar_sat_refutation,[],[f65,f218,f252,f257,f441,f459,f491,f510,f560,f666,f672,f675,f729,f732])).
% 1.50/0.56  fof(f732,plain,(
% 1.50/0.56    spl9_13 | ~spl9_32 | spl9_34),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f731])).
% 1.50/0.56  fof(f731,plain,(
% 1.50/0.56    $false | (spl9_13 | ~spl9_32 | spl9_34)),
% 1.50/0.56    inference(subsumption_resolution,[],[f730,f144])).
% 1.50/0.56  fof(f144,plain,(
% 1.50/0.56    ~v1_xboole_0(sK4) | spl9_13),
% 1.50/0.56    inference(resolution,[],[f134,f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.50/0.56  fof(f134,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | spl9_13),
% 1.50/0.56    inference(resolution,[],[f131,f36])).
% 1.50/0.56  fof(f131,plain,(
% 1.50/0.56    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl9_13),
% 1.50/0.56    inference(avatar_component_clause,[],[f129])).
% 1.50/0.56  fof(f129,plain,(
% 1.50/0.56    spl9_13 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.50/0.57  % (5679)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.57  fof(f730,plain,(
% 1.50/0.57    v1_xboole_0(sK4) | (~spl9_32 | spl9_34)),
% 1.50/0.57    inference(subsumption_resolution,[],[f725,f509])).
% 1.50/0.57  fof(f509,plain,(
% 1.50/0.57    ~r1_tarski(sK5,sK1) | spl9_34),
% 1.50/0.57    inference(avatar_component_clause,[],[f507])).
% 1.50/0.57  fof(f507,plain,(
% 1.50/0.57    spl9_34 <=> r1_tarski(sK5,sK1)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 1.50/0.57  fof(f725,plain,(
% 1.50/0.57    r1_tarski(sK5,sK1) | v1_xboole_0(sK4) | ~spl9_32),
% 1.50/0.57    inference(resolution,[],[f495,f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f16,plain,(
% 1.50/0.57    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f6])).
% 1.50/0.57  fof(f6,axiom,(
% 1.50/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 1.50/0.57  fof(f495,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) | ~spl9_32),
% 1.50/0.57    inference(avatar_component_clause,[],[f494])).
% 1.50/0.57  fof(f494,plain,(
% 1.50/0.57    spl9_32 <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1))),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.50/0.57  fof(f729,plain,(
% 1.50/0.57    spl9_6 | spl9_13 | ~spl9_32),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f728])).
% 1.50/0.57  fof(f728,plain,(
% 1.50/0.57    $false | (spl9_6 | spl9_13 | ~spl9_32)),
% 1.50/0.57    inference(subsumption_resolution,[],[f727,f143])).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    ~v1_xboole_0(sK5) | spl9_13),
% 1.50/0.57    inference(resolution,[],[f134,f37])).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f20])).
% 1.50/0.57  fof(f20,plain,(
% 1.50/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.50/0.57    inference(ennf_transformation,[],[f4])).
% 1.50/0.57  fof(f4,axiom,(
% 1.50/0.57    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.50/0.57  fof(f727,plain,(
% 1.50/0.57    v1_xboole_0(sK5) | (spl9_6 | ~spl9_32)),
% 1.50/0.57    inference(subsumption_resolution,[],[f724,f93])).
% 1.50/0.57  fof(f93,plain,(
% 1.50/0.57    ~r1_tarski(sK4,sK0) | spl9_6),
% 1.50/0.57    inference(avatar_component_clause,[],[f91])).
% 1.50/0.57  fof(f91,plain,(
% 1.50/0.57    spl9_6 <=> r1_tarski(sK4,sK0)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.50/0.57  fof(f724,plain,(
% 1.50/0.57    r1_tarski(sK4,sK0) | v1_xboole_0(sK5) | ~spl9_32),
% 1.50/0.57    inference(resolution,[],[f495,f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f16])).
% 1.50/0.57  fof(f675,plain,(
% 1.50/0.57    spl9_13 | ~spl9_28 | spl9_30),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f674])).
% 1.50/0.57  fof(f674,plain,(
% 1.50/0.57    $false | (spl9_13 | ~spl9_28 | spl9_30)),
% 1.50/0.57    inference(subsumption_resolution,[],[f673,f134])).
% 1.50/0.57  fof(f673,plain,(
% 1.50/0.57    v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | (~spl9_28 | spl9_30)),
% 1.50/0.57    inference(subsumption_resolution,[],[f668,f440])).
% 1.50/0.57  fof(f440,plain,(
% 1.50/0.57    ~r1_tarski(sK6,sK2) | spl9_30),
% 1.50/0.57    inference(avatar_component_clause,[],[f438])).
% 1.50/0.57  fof(f438,plain,(
% 1.50/0.57    spl9_30 <=> r1_tarski(sK6,sK2)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.50/0.57  fof(f668,plain,(
% 1.50/0.57    r1_tarski(sK6,sK2) | v1_xboole_0(k2_zfmisc_1(sK4,sK5)) | ~spl9_28),
% 1.50/0.57    inference(resolution,[],[f429,f30])).
% 1.50/0.57  fof(f429,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl9_28),
% 1.50/0.57    inference(avatar_component_clause,[],[f428])).
% 1.50/0.57  fof(f428,plain,(
% 1.50/0.57    spl9_28 <=> r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.50/0.57  fof(f672,plain,(
% 1.50/0.57    spl9_13 | ~spl9_28 | spl9_32),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f671])).
% 1.50/0.57  fof(f671,plain,(
% 1.50/0.57    $false | (spl9_13 | ~spl9_28 | spl9_32)),
% 1.50/0.57    inference(subsumption_resolution,[],[f670,f133])).
% 1.50/0.57  fof(f133,plain,(
% 1.50/0.57    ~v1_xboole_0(sK6) | spl9_13),
% 1.50/0.57    inference(resolution,[],[f131,f37])).
% 1.50/0.57  fof(f670,plain,(
% 1.50/0.57    v1_xboole_0(sK6) | (~spl9_28 | spl9_32)),
% 1.50/0.57    inference(subsumption_resolution,[],[f667,f496])).
% 1.50/0.57  fof(f496,plain,(
% 1.50/0.57    ~r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) | spl9_32),
% 1.50/0.57    inference(avatar_component_clause,[],[f494])).
% 1.50/0.57  fof(f667,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK6) | ~spl9_28),
% 1.50/0.57    inference(resolution,[],[f429,f31])).
% 1.50/0.57  fof(f666,plain,(
% 1.50/0.57    ~spl9_4 | spl9_12 | spl9_28),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f665])).
% 1.50/0.57  fof(f665,plain,(
% 1.50/0.57    $false | (~spl9_4 | spl9_12 | spl9_28)),
% 1.50/0.57    inference(subsumption_resolution,[],[f593,f430])).
% 1.50/0.57  fof(f430,plain,(
% 1.50/0.57    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl9_28),
% 1.50/0.57    inference(avatar_component_clause,[],[f428])).
% 1.50/0.57  fof(f593,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (~spl9_4 | spl9_12)),
% 1.50/0.57    inference(forward_demodulation,[],[f592,f406])).
% 1.50/0.57  fof(f406,plain,(
% 1.50/0.57    ( ! [X16] : (k1_relat_1(k2_zfmisc_1(X16,sK3)) = X16) ) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f328,f270])).
% 1.50/0.57  fof(f270,plain,(
% 1.50/0.57    ~v1_xboole_0(sK3) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f125,f37])).
% 1.50/0.57  fof(f125,plain,(
% 1.50/0.57    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | spl9_12),
% 1.50/0.57    inference(avatar_component_clause,[],[f124])).
% 1.50/0.57  fof(f124,plain,(
% 1.50/0.57    spl9_12 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.50/0.57  fof(f328,plain,(
% 1.50/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f324,f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 1.50/0.57  fof(f324,plain,(
% 1.50/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X0)),X1)) )),
% 1.50/0.57    inference(resolution,[],[f151,f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(flattening,[],[f23])).
% 1.50/0.57  fof(f23,plain,(
% 1.50/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.57    inference(nnf_transformation,[],[f3])).
% 1.50/0.57  fof(f3,axiom,(
% 1.50/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.57  fof(f151,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.50/0.57    inference(subsumption_resolution,[],[f145,f34])).
% 1.50/0.57  fof(f34,plain,(
% 1.50/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.50/0.57    inference(cnf_transformation,[],[f7])).
% 1.50/0.57  fof(f7,axiom,(
% 1.50/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.50/0.57  fof(f145,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.50/0.57    inference(resolution,[],[f31,f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f17])).
% 1.50/0.57  fof(f17,plain,(
% 1.50/0.57    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.50/0.57  fof(f592,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))) | (~spl9_4 | spl9_12)),
% 1.50/0.57    inference(subsumption_resolution,[],[f583,f270])).
% 1.50/0.57  fof(f583,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))) | v1_xboole_0(sK3) | ~spl9_4),
% 1.50/0.57    inference(superposition,[],[f151,f562])).
% 1.50/0.57  fof(f562,plain,(
% 1.50/0.57    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) | ~spl9_4),
% 1.50/0.57    inference(backward_demodulation,[],[f46,f63])).
% 1.50/0.57  fof(f63,plain,(
% 1.50/0.57    sK3 = sK7 | ~spl9_4),
% 1.50/0.57    inference(avatar_component_clause,[],[f62])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    spl9_4 <=> sK3 = sK7),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.50/0.57    inference(definition_unfolding,[],[f27,f44,f44])).
% 1.50/0.57  fof(f44,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.50/0.57    inference(definition_unfolding,[],[f42,f41])).
% 1.50/0.57  % (5680)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f10])).
% 1.50/0.57  fof(f10,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f11])).
% 1.50/0.57  fof(f11,axiom,(
% 1.50/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.50/0.57  fof(f27,plain,(
% 1.50/0.57    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f22,plain,(
% 1.50/0.57    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f21])).
% 1.50/0.57  fof(f21,plain,(
% 1.50/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f15,plain,(
% 1.50/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.50/0.57    inference(flattening,[],[f14])).
% 1.50/0.57  fof(f14,plain,(
% 1.50/0.57    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.50/0.57    inference(ennf_transformation,[],[f13])).
% 1.50/0.57  fof(f13,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.50/0.57    inference(negated_conjecture,[],[f12])).
% 1.50/0.57  fof(f12,conjecture,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.50/0.57  fof(f560,plain,(
% 1.50/0.57    spl9_12 | spl9_31),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f559])).
% 1.50/0.57  fof(f559,plain,(
% 1.50/0.57    $false | (spl9_12 | spl9_31)),
% 1.50/0.57    inference(subsumption_resolution,[],[f558,f271])).
% 1.50/0.57  fof(f271,plain,(
% 1.50/0.57    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f125,f36])).
% 1.50/0.57  fof(f558,plain,(
% 1.50/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl9_31),
% 1.50/0.57    inference(subsumption_resolution,[],[f554,f458])).
% 1.50/0.57  fof(f458,plain,(
% 1.50/0.57    ~r1_tarski(sK3,sK7) | spl9_31),
% 1.50/0.57    inference(avatar_component_clause,[],[f456])).
% 1.50/0.57  fof(f456,plain,(
% 1.50/0.57    spl9_31 <=> r1_tarski(sK3,sK7)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.50/0.57  fof(f554,plain,(
% 1.50/0.57    r1_tarski(sK3,sK7) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.50/0.57    inference(resolution,[],[f140,f47])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.57    inference(equality_resolution,[],[f39])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f140,plain,(
% 1.50/0.57    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(X3,X4),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | r1_tarski(X4,sK7) | v1_xboole_0(X3)) )),
% 1.50/0.57    inference(superposition,[],[f30,f46])).
% 1.50/0.57  fof(f510,plain,(
% 1.50/0.57    ~spl9_34 | spl9_2 | spl9_12),
% 1.50/0.57    inference(avatar_split_clause,[],[f505,f124,f54,f507])).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    spl9_2 <=> sK1 = sK5),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.50/0.57  fof(f505,plain,(
% 1.50/0.57    sK1 = sK5 | ~r1_tarski(sK5,sK1) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f492,f40])).
% 1.50/0.57  % (5662)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.57  fof(f492,plain,(
% 1.50/0.57    r1_tarski(sK1,sK5) | spl9_12),
% 1.50/0.57    inference(subsumption_resolution,[],[f487,f287])).
% 1.50/0.57  fof(f287,plain,(
% 1.50/0.57    ~v1_xboole_0(sK0) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f282,f36])).
% 1.50/0.57  fof(f282,plain,(
% 1.50/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f271,f36])).
% 1.50/0.57  fof(f487,plain,(
% 1.50/0.57    r1_tarski(sK1,sK5) | v1_xboole_0(sK0) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f425,f30])).
% 1.50/0.57  fof(f425,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl9_12),
% 1.50/0.57    inference(subsumption_resolution,[],[f422,f281])).
% 1.50/0.57  fof(f281,plain,(
% 1.50/0.57    ~v1_xboole_0(sK2) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f271,f37])).
% 1.50/0.57  fof(f422,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | v1_xboole_0(sK2) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f411,f31])).
% 1.50/0.57  fof(f411,plain,(
% 1.50/0.57    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl9_12),
% 1.50/0.57    inference(backward_demodulation,[],[f117,f406])).
% 1.50/0.57  fof(f117,plain,(
% 1.50/0.57    r1_tarski(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.50/0.57    inference(superposition,[],[f35,f46])).
% 1.50/0.57  fof(f491,plain,(
% 1.50/0.57    spl9_5 | spl9_12),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f490])).
% 1.50/0.57  fof(f490,plain,(
% 1.50/0.57    $false | (spl9_5 | spl9_12)),
% 1.50/0.57    inference(subsumption_resolution,[],[f489,f286])).
% 1.50/0.57  fof(f286,plain,(
% 1.50/0.57    ~v1_xboole_0(sK1) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f282,f37])).
% 1.50/0.57  fof(f489,plain,(
% 1.50/0.57    v1_xboole_0(sK1) | (spl9_5 | spl9_12)),
% 1.50/0.57    inference(subsumption_resolution,[],[f486,f89])).
% 1.50/0.57  fof(f89,plain,(
% 1.50/0.57    ~r1_tarski(sK0,sK4) | spl9_5),
% 1.50/0.57    inference(avatar_component_clause,[],[f87])).
% 1.50/0.57  fof(f87,plain,(
% 1.50/0.57    spl9_5 <=> r1_tarski(sK0,sK4)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.50/0.57  fof(f486,plain,(
% 1.50/0.57    r1_tarski(sK0,sK4) | v1_xboole_0(sK1) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f425,f31])).
% 1.50/0.57  fof(f459,plain,(
% 1.50/0.57    ~spl9_31 | spl9_4 | spl9_13),
% 1.50/0.57    inference(avatar_split_clause,[],[f454,f129,f62,f456])).
% 1.50/0.57  fof(f454,plain,(
% 1.50/0.57    sK3 = sK7 | ~r1_tarski(sK3,sK7) | spl9_13),
% 1.50/0.57    inference(resolution,[],[f450,f40])).
% 1.50/0.57  fof(f450,plain,(
% 1.50/0.57    r1_tarski(sK7,sK3) | spl9_13),
% 1.50/0.57    inference(resolution,[],[f142,f47])).
% 1.50/0.57  fof(f142,plain,(
% 1.50/0.57    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X3,X4)) | r1_tarski(sK7,X4)) ) | spl9_13),
% 1.50/0.57    inference(subsumption_resolution,[],[f138,f131])).
% 1.50/0.57  fof(f138,plain,(
% 1.50/0.57    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(X3,X4)) | r1_tarski(sK7,X4) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))) )),
% 1.50/0.57    inference(superposition,[],[f30,f46])).
% 1.50/0.57  fof(f441,plain,(
% 1.50/0.57    ~spl9_30 | spl9_3 | spl9_12),
% 1.50/0.57    inference(avatar_split_clause,[],[f436,f124,f58,f438])).
% 1.50/0.57  % (5680)Refutation not found, incomplete strategy% (5680)------------------------------
% 1.50/0.57  % (5680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (5680)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (5680)Memory used [KB]: 6268
% 1.50/0.57  % (5680)Time elapsed: 0.152 s
% 1.50/0.57  % (5680)------------------------------
% 1.50/0.57  % (5680)------------------------------
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    spl9_3 <=> sK2 = sK6),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.50/0.57  fof(f436,plain,(
% 1.50/0.57    sK2 = sK6 | ~r1_tarski(sK6,sK2) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f426,f40])).
% 1.50/0.57  fof(f426,plain,(
% 1.50/0.57    r1_tarski(sK2,sK6) | spl9_12),
% 1.50/0.57    inference(subsumption_resolution,[],[f423,f282])).
% 1.50/0.57  fof(f423,plain,(
% 1.50/0.57    r1_tarski(sK2,sK6) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl9_12),
% 1.50/0.57    inference(resolution,[],[f411,f30])).
% 1.50/0.57  fof(f257,plain,(
% 1.50/0.57    ~spl9_13 | spl9_12),
% 1.50/0.57    inference(avatar_split_clause,[],[f254,f124,f129])).
% 1.50/0.57  fof(f254,plain,(
% 1.50/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 1.50/0.57    inference(superposition,[],[f36,f46])).
% 1.50/0.57  fof(f252,plain,(
% 1.50/0.57    ~spl9_12),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f251])).
% 1.50/0.57  fof(f251,plain,(
% 1.50/0.57    $false | ~spl9_12),
% 1.50/0.57    inference(subsumption_resolution,[],[f245,f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.50/0.57    inference(definition_unfolding,[],[f28,f44])).
% 1.50/0.57  fof(f28,plain,(
% 1.50/0.57    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.50/0.57    inference(cnf_transformation,[],[f22])).
% 1.50/0.57  fof(f245,plain,(
% 1.50/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl9_12),
% 1.50/0.57    inference(resolution,[],[f126,f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.50/0.57    inference(cnf_transformation,[],[f18])).
% 1.50/0.57  fof(f18,plain,(
% 1.50/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f1])).
% 1.50/0.57  fof(f1,axiom,(
% 1.50/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.50/0.57  fof(f126,plain,(
% 1.50/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl9_12),
% 1.50/0.57    inference(avatar_component_clause,[],[f124])).
% 1.68/0.57  % (5664)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.68/0.57  fof(f218,plain,(
% 1.68/0.57    ~spl9_6 | ~spl9_5 | spl9_1),
% 1.68/0.57    inference(avatar_split_clause,[],[f216,f50,f87,f91])).
% 1.68/0.57  fof(f50,plain,(
% 1.68/0.57    spl9_1 <=> sK0 = sK4),
% 1.68/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.68/0.57  fof(f216,plain,(
% 1.68/0.57    ~r1_tarski(sK0,sK4) | ~r1_tarski(sK4,sK0) | spl9_1),
% 1.68/0.57    inference(extensionality_resolution,[],[f40,f52])).
% 1.68/0.57  fof(f52,plain,(
% 1.68/0.57    sK0 != sK4 | spl9_1),
% 1.68/0.57    inference(avatar_component_clause,[],[f50])).
% 1.68/0.57  fof(f65,plain,(
% 1.68/0.57    ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 1.68/0.57    inference(avatar_split_clause,[],[f29,f62,f58,f54,f50])).
% 1.68/0.57  fof(f29,plain,(
% 1.68/0.57    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 1.68/0.57    inference(cnf_transformation,[],[f22])).
% 1.68/0.57  % SZS output end Proof for theBenchmark
% 1.68/0.57  % (5659)------------------------------
% 1.68/0.57  % (5659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.57  % (5659)Termination reason: Refutation
% 1.68/0.57  
% 1.68/0.57  % (5659)Memory used [KB]: 11001
% 1.68/0.57  % (5659)Time elapsed: 0.155 s
% 1.68/0.57  % (5659)------------------------------
% 1.68/0.57  % (5659)------------------------------
% 1.68/0.57  % (5678)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.68/0.58  % (5683)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.58  % (5652)Success in time 0.212 s
%------------------------------------------------------------------------------

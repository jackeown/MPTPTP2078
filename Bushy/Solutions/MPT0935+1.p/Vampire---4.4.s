%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t96_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :   24 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f112])).

fof(f112,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f110,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X1) = k1_relat_1(k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X3))) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',fc7_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | k2_tarski(X0,X2) = k1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',t24_relat_1)).

fof(f110,plain,
    ( k2_tarski(sK0,sK3) != k1_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK3,sK4)))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f106,f40])).

fof(f40,plain,
    ( k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5))))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl6_1
  <=> k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)) = k1_relat_1(k2_tarski(k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2))) ),
    inference(superposition,[],[f67,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',d3_mcart_1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k2_tarski(k4_tarski(X0,X1),X3) = k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k4_tarski(X3,X4))) ),
    inference(superposition,[],[f52,f27])).

fof(f41,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f39])).

fof(f26,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) != k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t96_mcart_1.p',t96_mcart_1)).
%------------------------------------------------------------------------------

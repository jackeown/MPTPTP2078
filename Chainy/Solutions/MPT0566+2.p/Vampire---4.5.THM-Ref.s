%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0566+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  45 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 (  92 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1005,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f936,f940,f989,f998,f1004])).

fof(f1004,plain,
    ( ~ spl11_2
    | spl11_11 ),
    inference(avatar_contradiction_clause,[],[f1003])).

fof(f1003,plain,
    ( $false
    | ~ spl11_2
    | spl11_11 ),
    inference(subsumption_resolution,[],[f1000,f939])).

fof(f939,plain,
    ( v1_relat_1(sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl11_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1000,plain,
    ( ~ v1_relat_1(sK1)
    | spl11_11 ),
    inference(resolution,[],[f997,f914])).

fof(f914,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f849])).

fof(f849,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f997,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl11_11 ),
    inference(avatar_component_clause,[],[f996])).

fof(f996,plain,
    ( spl11_11
  <=> r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f998,plain,
    ( ~ spl11_11
    | spl11_1
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f993,f987,f934,f996])).

fof(f934,plain,
    ( spl11_1
  <=> r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f987,plain,
    ( spl11_10
  <=> k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f993,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl11_1
    | ~ spl11_10 ),
    inference(backward_demodulation,[],[f935,f988])).

fof(f988,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f987])).

fof(f935,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f934])).

fof(f989,plain,
    ( spl11_10
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f985,f938,f987])).

fof(f985,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl11_2 ),
    inference(resolution,[],[f921,f939])).

fof(f921,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f851])).

fof(f851,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f752])).

fof(f752,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f940,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f877,f938])).

fof(f877,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f853])).

fof(f853,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f822,f852])).

fof(f852,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f822,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f754])).

fof(f754,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f753])).

fof(f753,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f936,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f878,f934])).

fof(f878,plain,(
    ~ r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f853])).
%------------------------------------------------------------------------------

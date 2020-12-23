%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:55 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 354 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  250 ( 786 expanded)
%              Number of equality atoms :   59 ( 176 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f152,f310,f312,f850,f6840])).

fof(f6840,plain,
    ( ~ spl2_5
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f6836])).

fof(f6836,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(resolution,[],[f6821,f52])).

fof(f52,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f48])).

fof(f48,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f6821,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(superposition,[],[f6803,f6519])).

fof(f6519,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f6453,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f6453,plain,
    ( k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(superposition,[],[f59,f6419])).

fof(f6419,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f6397,f6238])).

fof(f6238,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f6237,f313])).

fof(f313,plain,
    ( k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f309,f236])).

fof(f236,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4) ) ),
    inference(forward_demodulation,[],[f235,f139])).

fof(f139,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X4)) ),
    inference(resolution,[],[f71,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f235,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k6_relat_1(X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)) ) ),
    inference(forward_demodulation,[],[f231,f60])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f231,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X5)
      | k6_relat_1(X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)) ) ),
    inference(resolution,[],[f75,f58])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f309,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl2_10
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f6237,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f6218,f87])).

fof(f87,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f6218,plain,
    ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k1_xboole_0))
    | ~ spl2_10 ),
    inference(superposition,[],[f6217,f87])).

fof(f6217,plain,
    ( ! [X324] : k7_relat_1(k6_relat_1(sK0),k6_subset_1(k1_relat_1(sK1),X324)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,X324))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f5238,f5237])).

fof(f5237,plain,
    ( ! [X323] : k6_subset_1(k6_relat_1(sK0),k7_relat_1(k6_relat_1(sK0),X323)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,X323))
    | ~ spl2_10 ),
    inference(resolution,[],[f993,f309])).

fof(f993,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,X7)
      | k6_subset_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X6),X8)) = k7_relat_1(k6_relat_1(X6),k6_subset_1(X7,X8)) ) ),
    inference(forward_demodulation,[],[f990,f59])).

fof(f990,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X6)),X7)
      | k6_subset_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X6),X8)) = k7_relat_1(k6_relat_1(X6),k6_subset_1(X7,X8)) ) ),
    inference(resolution,[],[f78,f58])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f5238,plain,(
    ! [X324] : k6_subset_1(k6_relat_1(sK0),k7_relat_1(k6_relat_1(sK0),X324)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(k1_relat_1(sK1),X324)) ),
    inference(resolution,[],[f993,f51])).

fof(f51,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6397,plain,
    ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(superposition,[],[f6285,f4262])).

fof(f4262,plain,(
    ! [X6] : k7_relat_1(k6_relat_1(X6),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X6),k1_relat_1(k7_relat_1(sK1,X6))) ),
    inference(resolution,[],[f761,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f761,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k7_relat_1(k6_relat_1(X5),k1_relat_1(X4)) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(X4,X5))) ) ),
    inference(forward_demodulation,[],[f758,f59])).

fof(f758,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k7_relat_1(k6_relat_1(X5),k1_relat_1(X4)) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(X4,k1_relat_1(k6_relat_1(X5))))) ) ),
    inference(resolution,[],[f64,f58])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f6285,plain,
    ( k7_relat_1(k6_relat_1(sK0),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(resolution,[],[f6268,f236])).

fof(f6268,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0)
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f6254,f59])).

fof(f6254,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k6_relat_1(sK0)))
    | ~ spl2_10
    | ~ spl2_18 ),
    inference(superposition,[],[f849,f6238])).

fof(f849,plain,
    ( ! [X23] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1))))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f848])).

fof(f848,plain,
    ( spl2_18
  <=> ! [X23] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f6803,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ spl2_5 ),
    inference(superposition,[],[f6789,f3927])).

fof(f3927,plain,(
    ! [X6] : k1_relat_1(k7_relat_1(sK1,X6)) = k10_relat_1(k7_relat_1(sK1,X6),k9_relat_1(sK1,X6)) ),
    inference(forward_demodulation,[],[f3924,f176])).

fof(f176,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f3924,plain,(
    ! [X6] : k1_relat_1(k7_relat_1(sK1,X6)) = k10_relat_1(k7_relat_1(sK1,X6),k2_relat_1(k7_relat_1(sK1,X6))) ),
    inference(resolution,[],[f91,f50])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f61,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f6789,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))
    | ~ spl2_5 ),
    inference(resolution,[],[f6788,f149])).

fof(f149,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl2_5
  <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f6788,plain,(
    ! [X12,X11] :
      ( ~ r1_tarski(k7_relat_1(sK1,X11),sK1)
      | r1_tarski(k10_relat_1(k7_relat_1(sK1,X11),X12),k10_relat_1(sK1,X12)) ) ),
    inference(resolution,[],[f6281,f50])).

fof(f6281,plain,(
    ! [X17,X15,X16] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k10_relat_1(k7_relat_1(sK1,X16),X17),k10_relat_1(X15,X17))
      | ~ r1_tarski(k7_relat_1(sK1,X16),X15) ) ),
    inference(resolution,[],[f360,f50])).

fof(f360,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X4)
      | r1_tarski(k10_relat_1(k7_relat_1(X2,X3),X5),k10_relat_1(X4,X5))
      | ~ r1_tarski(k7_relat_1(X2,X3),X4) ) ),
    inference(resolution,[],[f76,f69])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(f850,plain,
    ( ~ spl2_4
    | spl2_18 ),
    inference(avatar_split_clause,[],[f829,f848,f144])).

fof(f144,plain,
    ( spl2_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f829,plain,(
    ! [X23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1))))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f70,f767])).

fof(f767,plain,(
    ! [X2] : k7_relat_1(sK1,X2) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f764,f59])).

fof(f764,plain,(
    ! [X2] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1)))) ),
    inference(resolution,[],[f759,f58])).

fof(f759,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k7_relat_1(sK1,k1_relat_1(X6)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X6,k1_relat_1(sK1)))) ) ),
    inference(resolution,[],[f64,f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f312,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f305,f58])).

fof(f305,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl2_9
  <=> v1_relat_1(k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f310,plain,
    ( ~ spl2_9
    | spl2_10 ),
    inference(avatar_split_clause,[],[f293,f307,f303])).

fof(f293,plain,
    ( r1_tarski(sK0,sK0)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f289,f59])).

fof(f289,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),sK0)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK1))) ),
    inference(superposition,[],[f70,f282])).

fof(f282,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f236,f51])).

fof(f152,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f146,f50])).

fof(f146,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f150,plain,
    ( ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f142,f148,f144])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK1,X0),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f74,f140])).

fof(f140,plain,(
    ! [X6] : k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1) ),
    inference(resolution,[],[f71,f50])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21400)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (21393)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (21399)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (21390)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.53  % (21394)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.53  % (21392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.53  % (21395)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (21402)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.54  % (21404)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.34/0.54  % (21401)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.34/0.54  % (21396)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.34/0.55  % (21389)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.34/0.55  % (21406)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.34/0.55  % (21397)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.34/0.55  % (21403)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.34/0.55  % (21398)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.58/0.56  % (21391)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.58/0.57  % (21407)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 3.12/0.80  % (21391)Refutation found. Thanks to Tanya!
% 3.12/0.80  % SZS status Theorem for theBenchmark
% 3.57/0.82  % SZS output start Proof for theBenchmark
% 3.57/0.82  fof(f6842,plain,(
% 3.57/0.82    $false),
% 3.57/0.82    inference(avatar_sat_refutation,[],[f150,f152,f310,f312,f850,f6840])).
% 3.57/0.82  fof(f6840,plain,(
% 3.57/0.82    ~spl2_5 | ~spl2_10 | ~spl2_18),
% 3.57/0.82    inference(avatar_contradiction_clause,[],[f6836])).
% 3.57/0.82  fof(f6836,plain,(
% 3.57/0.82    $false | (~spl2_5 | ~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(resolution,[],[f6821,f52])).
% 3.57/0.82  fof(f52,plain,(
% 3.57/0.82    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.57/0.82    inference(cnf_transformation,[],[f49])).
% 3.57/0.82  fof(f49,plain,(
% 3.57/0.82    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.57/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f48])).
% 3.57/0.82  fof(f48,plain,(
% 3.57/0.82    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.57/0.82    introduced(choice_axiom,[])).
% 3.57/0.82  fof(f30,plain,(
% 3.57/0.82    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.57/0.82    inference(flattening,[],[f29])).
% 3.57/0.82  fof(f29,plain,(
% 3.57/0.82    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f27])).
% 3.57/0.82  fof(f27,negated_conjecture,(
% 3.57/0.82    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.57/0.82    inference(negated_conjecture,[],[f26])).
% 3.57/0.82  fof(f26,conjecture,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 3.57/0.82  fof(f6821,plain,(
% 3.57/0.82    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | (~spl2_5 | ~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(superposition,[],[f6803,f6519])).
% 3.57/0.82  fof(f6519,plain,(
% 3.57/0.82    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(forward_demodulation,[],[f6453,f59])).
% 3.57/0.82  fof(f59,plain,(
% 3.57/0.82    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.57/0.82    inference(cnf_transformation,[],[f20])).
% 3.57/0.82  fof(f20,axiom,(
% 3.57/0.82    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.57/0.82  fof(f6453,plain,(
% 3.57/0.82    k1_relat_1(k6_relat_1(sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(superposition,[],[f59,f6419])).
% 3.57/0.82  fof(f6419,plain,(
% 3.57/0.82    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(forward_demodulation,[],[f6397,f6238])).
% 3.57/0.82  fof(f6238,plain,(
% 3.57/0.82    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_10),
% 3.57/0.82    inference(forward_demodulation,[],[f6237,f313])).
% 3.57/0.82  fof(f313,plain,(
% 3.57/0.82    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),sK0) | ~spl2_10),
% 3.57/0.82    inference(resolution,[],[f309,f236])).
% 3.57/0.82  fof(f236,plain,(
% 3.57/0.82    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k6_relat_1(X4) = k7_relat_1(k6_relat_1(X5),X4)) )),
% 3.57/0.82    inference(forward_demodulation,[],[f235,f139])).
% 3.57/0.82  fof(f139,plain,(
% 3.57/0.82    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) )),
% 3.57/0.82    inference(resolution,[],[f71,f58])).
% 3.57/0.82  fof(f58,plain,(
% 3.57/0.82    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.57/0.82    inference(cnf_transformation,[],[f28])).
% 3.57/0.82  fof(f28,plain,(
% 3.57/0.82    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.57/0.82    inference(pure_predicate_removal,[],[f25])).
% 3.57/0.82  fof(f25,axiom,(
% 3.57/0.82    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.57/0.82  fof(f71,plain,(
% 3.57/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f37])).
% 3.57/0.82  fof(f37,plain,(
% 3.57/0.82    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f24])).
% 3.57/0.82  fof(f24,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.57/0.82  fof(f235,plain,(
% 3.57/0.82    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k6_relat_1(X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) )),
% 3.57/0.82    inference(forward_demodulation,[],[f231,f60])).
% 3.57/0.82  fof(f60,plain,(
% 3.57/0.82    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.57/0.82    inference(cnf_transformation,[],[f20])).
% 3.57/0.82  fof(f231,plain,(
% 3.57/0.82    ( ! [X4,X5] : (~r1_tarski(k2_relat_1(k6_relat_1(X4)),X5) | k6_relat_1(X4) = k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) )),
% 3.57/0.82    inference(resolution,[],[f75,f58])).
% 3.57/0.82  fof(f75,plain,(
% 3.57/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 3.57/0.82    inference(cnf_transformation,[],[f41])).
% 3.57/0.82  fof(f41,plain,(
% 3.57/0.82    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(flattening,[],[f40])).
% 3.57/0.82  fof(f40,plain,(
% 3.57/0.82    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f22])).
% 3.57/0.82  fof(f22,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 3.57/0.82  fof(f309,plain,(
% 3.57/0.82    r1_tarski(sK0,sK0) | ~spl2_10),
% 3.57/0.82    inference(avatar_component_clause,[],[f307])).
% 3.57/0.82  fof(f307,plain,(
% 3.57/0.82    spl2_10 <=> r1_tarski(sK0,sK0)),
% 3.57/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.57/0.82  fof(f6237,plain,(
% 3.57/0.82    k7_relat_1(k6_relat_1(sK0),sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_10),
% 3.57/0.82    inference(forward_demodulation,[],[f6218,f87])).
% 3.57/0.82  fof(f87,plain,(
% 3.57/0.82    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.57/0.82    inference(definition_unfolding,[],[f57,f65])).
% 3.57/0.82  fof(f65,plain,(
% 3.57/0.82    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f10])).
% 3.57/0.82  fof(f10,axiom,(
% 3.57/0.82    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.57/0.82  fof(f57,plain,(
% 3.57/0.82    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.57/0.82    inference(cnf_transformation,[],[f5])).
% 3.57/0.82  fof(f5,axiom,(
% 3.57/0.82    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.57/0.82  fof(f6218,plain,(
% 3.57/0.82    k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,k1_xboole_0)) | ~spl2_10),
% 3.57/0.82    inference(superposition,[],[f6217,f87])).
% 3.57/0.82  fof(f6217,plain,(
% 3.57/0.82    ( ! [X324] : (k7_relat_1(k6_relat_1(sK0),k6_subset_1(k1_relat_1(sK1),X324)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,X324))) ) | ~spl2_10),
% 3.57/0.82    inference(forward_demodulation,[],[f5238,f5237])).
% 3.57/0.82  fof(f5237,plain,(
% 3.57/0.82    ( ! [X323] : (k6_subset_1(k6_relat_1(sK0),k7_relat_1(k6_relat_1(sK0),X323)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(sK0,X323))) ) | ~spl2_10),
% 3.57/0.82    inference(resolution,[],[f993,f309])).
% 3.57/0.82  fof(f993,plain,(
% 3.57/0.82    ( ! [X6,X8,X7] : (~r1_tarski(X6,X7) | k6_subset_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X6),X8)) = k7_relat_1(k6_relat_1(X6),k6_subset_1(X7,X8))) )),
% 3.57/0.82    inference(forward_demodulation,[],[f990,f59])).
% 3.57/0.82  fof(f990,plain,(
% 3.57/0.82    ( ! [X6,X8,X7] : (~r1_tarski(k1_relat_1(k6_relat_1(X6)),X7) | k6_subset_1(k6_relat_1(X6),k7_relat_1(k6_relat_1(X6),X8)) = k7_relat_1(k6_relat_1(X6),k6_subset_1(X7,X8))) )),
% 3.57/0.82    inference(resolution,[],[f78,f58])).
% 3.57/0.82  fof(f78,plain,(
% 3.57/0.82    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 3.57/0.82    inference(cnf_transformation,[],[f45])).
% 3.57/0.82  fof(f45,plain,(
% 3.57/0.82    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.57/0.82    inference(flattening,[],[f44])).
% 3.57/0.82  fof(f44,plain,(
% 3.57/0.82    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 3.57/0.82    inference(ennf_transformation,[],[f17])).
% 3.57/0.82  fof(f17,axiom,(
% 3.57/0.82    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 3.57/0.82  fof(f5238,plain,(
% 3.57/0.82    ( ! [X324] : (k6_subset_1(k6_relat_1(sK0),k7_relat_1(k6_relat_1(sK0),X324)) = k7_relat_1(k6_relat_1(sK0),k6_subset_1(k1_relat_1(sK1),X324))) )),
% 3.57/0.82    inference(resolution,[],[f993,f51])).
% 3.57/0.82  fof(f51,plain,(
% 3.57/0.82    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.57/0.82    inference(cnf_transformation,[],[f49])).
% 3.57/0.82  fof(f6397,plain,(
% 3.57/0.82    k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(superposition,[],[f6285,f4262])).
% 3.57/0.82  fof(f4262,plain,(
% 3.57/0.82    ( ! [X6] : (k7_relat_1(k6_relat_1(X6),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X6),k1_relat_1(k7_relat_1(sK1,X6)))) )),
% 3.57/0.82    inference(resolution,[],[f761,f50])).
% 3.57/0.82  fof(f50,plain,(
% 3.57/0.82    v1_relat_1(sK1)),
% 3.57/0.82    inference(cnf_transformation,[],[f49])).
% 3.57/0.82  fof(f761,plain,(
% 3.57/0.82    ( ! [X4,X5] : (~v1_relat_1(X4) | k7_relat_1(k6_relat_1(X5),k1_relat_1(X4)) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(X4,X5)))) )),
% 3.57/0.82    inference(forward_demodulation,[],[f758,f59])).
% 3.57/0.82  fof(f758,plain,(
% 3.57/0.82    ( ! [X4,X5] : (~v1_relat_1(X4) | k7_relat_1(k6_relat_1(X5),k1_relat_1(X4)) = k7_relat_1(k6_relat_1(X5),k1_relat_1(k7_relat_1(X4,k1_relat_1(k6_relat_1(X5)))))) )),
% 3.57/0.82    inference(resolution,[],[f64,f58])).
% 3.57/0.82  fof(f64,plain,(
% 3.57/0.82    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 3.57/0.82    inference(cnf_transformation,[],[f34])).
% 3.57/0.82  fof(f34,plain,(
% 3.57/0.82    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.57/0.82    inference(ennf_transformation,[],[f16])).
% 3.57/0.82  fof(f16,axiom,(
% 3.57/0.82    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 3.57/0.82  fof(f6285,plain,(
% 3.57/0.82    k7_relat_1(k6_relat_1(sK0),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,sK0))) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(resolution,[],[f6268,f236])).
% 3.57/0.82  fof(f6268,plain,(
% 3.57/0.82    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),sK0) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(forward_demodulation,[],[f6254,f59])).
% 3.57/0.82  fof(f6254,plain,(
% 3.57/0.82    r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k6_relat_1(sK0))) | (~spl2_10 | ~spl2_18)),
% 3.57/0.82    inference(superposition,[],[f849,f6238])).
% 3.57/0.82  fof(f849,plain,(
% 3.57/0.82    ( ! [X23] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1))))) ) | ~spl2_18),
% 3.57/0.82    inference(avatar_component_clause,[],[f848])).
% 3.57/0.82  fof(f848,plain,(
% 3.57/0.82    spl2_18 <=> ! [X23] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1))))),
% 3.57/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.57/0.82  fof(f6803,plain,(
% 3.57/0.82    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_5),
% 3.57/0.82    inference(superposition,[],[f6789,f3927])).
% 3.57/0.82  fof(f3927,plain,(
% 3.57/0.82    ( ! [X6] : (k1_relat_1(k7_relat_1(sK1,X6)) = k10_relat_1(k7_relat_1(sK1,X6),k9_relat_1(sK1,X6))) )),
% 3.57/0.82    inference(forward_demodulation,[],[f3924,f176])).
% 3.57/0.82  fof(f176,plain,(
% 3.57/0.82    ( ! [X6] : (k2_relat_1(k7_relat_1(sK1,X6)) = k9_relat_1(sK1,X6)) )),
% 3.57/0.82    inference(resolution,[],[f72,f50])).
% 3.57/0.82  fof(f72,plain,(
% 3.57/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f38])).
% 3.57/0.82  fof(f38,plain,(
% 3.57/0.82    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f13])).
% 3.57/0.82  fof(f13,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.57/0.82  fof(f3924,plain,(
% 3.57/0.82    ( ! [X6] : (k1_relat_1(k7_relat_1(sK1,X6)) = k10_relat_1(k7_relat_1(sK1,X6),k2_relat_1(k7_relat_1(sK1,X6)))) )),
% 3.57/0.82    inference(resolution,[],[f91,f50])).
% 3.57/0.82  fof(f91,plain,(
% 3.57/0.82    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) = k1_relat_1(k7_relat_1(X1,X2))) )),
% 3.57/0.82    inference(resolution,[],[f61,f69])).
% 3.57/0.82  fof(f69,plain,(
% 3.57/0.82    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f35])).
% 3.57/0.82  fof(f35,plain,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.57/0.82    inference(ennf_transformation,[],[f12])).
% 3.57/0.82  fof(f12,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.57/0.82  fof(f61,plain,(
% 3.57/0.82    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f31])).
% 3.57/0.82  fof(f31,plain,(
% 3.57/0.82    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.82    inference(ennf_transformation,[],[f14])).
% 3.57/0.82  fof(f14,axiom,(
% 3.57/0.82    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 3.57/0.82  fof(f6789,plain,(
% 3.57/0.82    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1))) ) | ~spl2_5),
% 3.57/0.82    inference(resolution,[],[f6788,f149])).
% 3.57/0.82  fof(f149,plain,(
% 3.57/0.82    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) ) | ~spl2_5),
% 3.57/0.82    inference(avatar_component_clause,[],[f148])).
% 3.57/0.82  fof(f148,plain,(
% 3.57/0.82    spl2_5 <=> ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)),
% 3.57/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.57/0.82  fof(f6788,plain,(
% 3.57/0.82    ( ! [X12,X11] : (~r1_tarski(k7_relat_1(sK1,X11),sK1) | r1_tarski(k10_relat_1(k7_relat_1(sK1,X11),X12),k10_relat_1(sK1,X12))) )),
% 3.57/0.82    inference(resolution,[],[f6281,f50])).
% 3.57/0.82  fof(f6281,plain,(
% 3.57/0.82    ( ! [X17,X15,X16] : (~v1_relat_1(X15) | r1_tarski(k10_relat_1(k7_relat_1(sK1,X16),X17),k10_relat_1(X15,X17)) | ~r1_tarski(k7_relat_1(sK1,X16),X15)) )),
% 3.57/0.82    inference(resolution,[],[f360,f50])).
% 3.57/0.82  fof(f360,plain,(
% 3.57/0.82    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X4) | r1_tarski(k10_relat_1(k7_relat_1(X2,X3),X5),k10_relat_1(X4,X5)) | ~r1_tarski(k7_relat_1(X2,X3),X4)) )),
% 3.57/0.82    inference(resolution,[],[f76,f69])).
% 3.57/0.82  fof(f76,plain,(
% 3.57/0.82    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))) )),
% 3.57/0.82    inference(cnf_transformation,[],[f43])).
% 3.57/0.82  fof(f43,plain,(
% 3.57/0.82    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(flattening,[],[f42])).
% 3.57/0.82  fof(f42,plain,(
% 3.57/0.82    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f15])).
% 3.57/0.82  fof(f15,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).
% 3.57/0.82  fof(f850,plain,(
% 3.57/0.82    ~spl2_4 | spl2_18),
% 3.57/0.82    inference(avatar_split_clause,[],[f829,f848,f144])).
% 3.57/0.82  fof(f144,plain,(
% 3.57/0.82    spl2_4 <=> v1_relat_1(sK1)),
% 3.57/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.57/0.82  fof(f829,plain,(
% 3.57/0.82    ( ! [X23] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X23)),k1_relat_1(k7_relat_1(k6_relat_1(X23),k1_relat_1(sK1)))) | ~v1_relat_1(sK1)) )),
% 3.57/0.82    inference(superposition,[],[f70,f767])).
% 3.57/0.82  fof(f767,plain,(
% 3.57/0.82    ( ! [X2] : (k7_relat_1(sK1,X2) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))))) )),
% 3.57/0.82    inference(forward_demodulation,[],[f764,f59])).
% 3.57/0.82  fof(f764,plain,(
% 3.57/0.82    ( ! [X2] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))))) )),
% 3.57/0.82    inference(resolution,[],[f759,f58])).
% 3.57/0.82  fof(f759,plain,(
% 3.57/0.82    ( ! [X6] : (~v1_relat_1(X6) | k7_relat_1(sK1,k1_relat_1(X6)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X6,k1_relat_1(sK1))))) )),
% 3.57/0.82    inference(resolution,[],[f64,f50])).
% 3.57/0.82  fof(f70,plain,(
% 3.57/0.82    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f36])).
% 3.57/0.82  fof(f36,plain,(
% 3.57/0.82    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f23])).
% 3.57/0.82  fof(f23,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 3.57/0.82  fof(f312,plain,(
% 3.57/0.82    spl2_9),
% 3.57/0.82    inference(avatar_contradiction_clause,[],[f311])).
% 3.57/0.82  fof(f311,plain,(
% 3.57/0.82    $false | spl2_9),
% 3.57/0.82    inference(resolution,[],[f305,f58])).
% 3.57/0.82  fof(f305,plain,(
% 3.57/0.82    ~v1_relat_1(k6_relat_1(k1_relat_1(sK1))) | spl2_9),
% 3.57/0.82    inference(avatar_component_clause,[],[f303])).
% 3.57/0.82  fof(f303,plain,(
% 3.57/0.82    spl2_9 <=> v1_relat_1(k6_relat_1(k1_relat_1(sK1)))),
% 3.57/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.57/0.82  fof(f310,plain,(
% 3.57/0.82    ~spl2_9 | spl2_10),
% 3.57/0.82    inference(avatar_split_clause,[],[f293,f307,f303])).
% 3.57/0.82  fof(f293,plain,(
% 3.57/0.82    r1_tarski(sK0,sK0) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK1)))),
% 3.57/0.82    inference(forward_demodulation,[],[f289,f59])).
% 3.57/0.82  fof(f289,plain,(
% 3.57/0.82    r1_tarski(k1_relat_1(k6_relat_1(sK0)),sK0) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK1)))),
% 3.57/0.82    inference(superposition,[],[f70,f282])).
% 3.57/0.82  fof(f282,plain,(
% 3.57/0.82    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 3.57/0.82    inference(resolution,[],[f236,f51])).
% 3.57/0.82  fof(f152,plain,(
% 3.57/0.82    spl2_4),
% 3.57/0.82    inference(avatar_contradiction_clause,[],[f151])).
% 3.57/0.82  fof(f151,plain,(
% 3.57/0.82    $false | spl2_4),
% 3.57/0.82    inference(resolution,[],[f146,f50])).
% 3.57/0.82  fof(f146,plain,(
% 3.57/0.82    ~v1_relat_1(sK1) | spl2_4),
% 3.57/0.82    inference(avatar_component_clause,[],[f144])).
% 3.57/0.82  fof(f150,plain,(
% 3.57/0.82    ~spl2_4 | spl2_5),
% 3.57/0.82    inference(avatar_split_clause,[],[f142,f148,f144])).
% 3.57/0.82  fof(f142,plain,(
% 3.57/0.82    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1) | ~v1_relat_1(sK1)) )),
% 3.57/0.82    inference(superposition,[],[f74,f140])).
% 3.57/0.82  fof(f140,plain,(
% 3.57/0.82    ( ! [X6] : (k7_relat_1(sK1,X6) = k5_relat_1(k6_relat_1(X6),sK1)) )),
% 3.57/0.82    inference(resolution,[],[f71,f50])).
% 3.57/0.82  fof(f74,plain,(
% 3.57/0.82    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 3.57/0.82    inference(cnf_transformation,[],[f39])).
% 3.57/0.82  fof(f39,plain,(
% 3.57/0.82    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.57/0.82    inference(ennf_transformation,[],[f21])).
% 3.57/0.82  fof(f21,axiom,(
% 3.57/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.57/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 3.57/0.82  % SZS output end Proof for theBenchmark
% 3.57/0.82  % (21391)------------------------------
% 3.57/0.82  % (21391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.57/0.82  % (21391)Termination reason: Refutation
% 3.57/0.82  
% 3.57/0.82  % (21391)Memory used [KB]: 9083
% 3.57/0.82  % (21391)Time elapsed: 0.369 s
% 3.57/0.82  % (21391)------------------------------
% 3.57/0.82  % (21391)------------------------------
% 3.57/0.82  % (21381)Success in time 0.455 s
%------------------------------------------------------------------------------

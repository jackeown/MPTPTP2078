%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:56 EST 2020

% Result     : Theorem 0.10s
% Output     : Refutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 255 expanded)
%              Number of leaves         :   17 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  207 ( 707 expanded)
%              Number of equality atoms :   54 ( 222 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f305,f1019,f1022,f1536])).

fof(f1536,plain,
    ( ~ spl2_14
    | ~ spl2_45 ),
    inference(avatar_contradiction_clause,[],[f1535])).

fof(f1535,plain,
    ( $false
    | ~ spl2_14
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f1531,f1051])).

fof(f1051,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f1050,f32])).

fof(f32,plain,(
    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f1050,plain,
    ( k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(resolution,[],[f1015,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f1015,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f1013,plain,
    ( spl2_45
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f1531,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_14 ),
    inference(superposition,[],[f1482,f53])).

fof(f53,plain,(
    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f1482,plain,
    ( ! [X1] : r1_tarski(k9_relat_1(sK1,k9_relat_1(sK0,X1)),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f792,f1224])).

fof(f1224,plain,
    ( ! [X3] : k9_relat_1(sK1,k9_relat_1(sK0,X3)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X3),sK1))
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f330,f1222])).

fof(f1222,plain,
    ( ! [X2] : k5_relat_1(k7_relat_1(sK0,X2),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2)
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f317,f200])).

fof(f200,plain,(
    ! [X2] : k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) = k5_relat_1(k7_relat_1(sK0,X2),sK1) ),
    inference(forward_demodulation,[],[f195,f50])).

fof(f50,plain,(
    ! [X3] : k7_relat_1(sK0,X3) = k5_relat_1(k6_relat_1(X3),sK0) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f195,plain,(
    ! [X2] : k5_relat_1(k5_relat_1(k6_relat_1(X2),sK0),sK1) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f131,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f131,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(X8,sK0),sK1) = k5_relat_1(X8,k5_relat_1(sK0,sK1)) ) ),
    inference(resolution,[],[f57,f30])).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k5_relat_1(k5_relat_1(X4,X5),sK1) = k5_relat_1(X4,k5_relat_1(X5,sK1))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f317,plain,
    ( ! [X2] : k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) = k7_relat_1(k5_relat_1(sK0,sK1),X2)
    | ~ spl2_14 ),
    inference(resolution,[],[f289,f39])).

fof(f289,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl2_14
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f330,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X3)) = k9_relat_1(sK1,k9_relat_1(sK0,X3))
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f318,f114])).

fof(f114,plain,(
    ! [X8] : k9_relat_1(k5_relat_1(sK0,sK1),X8) = k9_relat_1(sK1,k9_relat_1(sK0,X8)) ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f318,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X3)) = k9_relat_1(k5_relat_1(sK0,sK1),X3)
    | ~ spl2_14 ),
    inference(resolution,[],[f289,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f792,plain,
    ( ! [X1] : r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f791,f33])).

fof(f791,plain,
    ( ! [X1] :
        ( r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f788,f289])).

fof(f788,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(k5_relat_1(sK0,sK1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f36,f200])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1022,plain,(
    spl2_44 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | spl2_44 ),
    inference(subsumption_resolution,[],[f1020,f31])).

fof(f1020,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_44 ),
    inference(resolution,[],[f1011,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1011,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))
    | spl2_44 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f1009,plain,
    ( spl2_44
  <=> v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1019,plain,
    ( ~ spl2_44
    | spl2_45 ),
    inference(avatar_split_clause,[],[f1018,f1013,f1009])).

fof(f1018,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f1017,f55])).

fof(f55,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK1,X2)) = k9_relat_1(sK1,X2) ),
    inference(resolution,[],[f31,f40])).

fof(f1017,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f1006,f30])).

fof(f1006,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f36,f955])).

fof(f955,plain,(
    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0))) ),
    inference(superposition,[],[f312,f52])).

fof(f52,plain,(
    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f312,plain,(
    ! [X11] : k5_relat_1(k5_relat_1(sK0,k6_relat_1(X11)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X11)) ),
    inference(resolution,[],[f133,f30])).

fof(f133,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k7_relat_1(sK1,X4)) ) ),
    inference(forward_demodulation,[],[f129,f56])).

fof(f56,plain,(
    ! [X3] : k7_relat_1(sK1,X3) = k5_relat_1(k6_relat_1(X3),sK1) ),
    inference(resolution,[],[f31,f39])).

fof(f129,plain,(
    ! [X4,X3] :
      ( k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK1))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f57,f33])).

fof(f305,plain,(
    spl2_14 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl2_14 ),
    inference(subsumption_resolution,[],[f303,f30])).

fof(f303,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_14 ),
    inference(subsumption_resolution,[],[f302,f31])).

fof(f302,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl2_14 ),
    inference(resolution,[],[f290,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f290,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n020.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 14:22:37 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.33  % (10407)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.10/0.33  % (10408)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.10/0.33  % (10417)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.10/0.33  % (10419)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.10/0.33  % (10418)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.10/0.33  % (10420)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.10/0.34  % (10413)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.10/0.35  % (10422)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.10/0.35  % (10431)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.10/0.35  % (10410)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.10/0.35  % (10421)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.10/0.35  % (10411)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.10/0.35  % (10416)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.10/0.35  % (10412)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.10/0.37  % (10430)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.10/0.37  % (10409)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.10/0.37  % (10429)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.10/0.37  % (10414)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.10/0.37  % (10427)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.10/0.38  % (10428)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.10/0.38  % (10425)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.10/0.38  % (10426)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.10/0.38  % (10424)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.10/0.39  % (10434)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.10/0.40  % (10415)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.10/0.42  % (10408)Refutation found. Thanks to Tanya!
% 0.10/0.42  % SZS status Theorem for theBenchmark
% 0.10/0.42  % SZS output start Proof for theBenchmark
% 0.10/0.42  fof(f1537,plain,(
% 0.10/0.42    $false),
% 0.10/0.42    inference(avatar_sat_refutation,[],[f305,f1019,f1022,f1536])).
% 0.10/0.42  fof(f1536,plain,(
% 0.10/0.42    ~spl2_14 | ~spl2_45),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f1535])).
% 0.10/0.42  fof(f1535,plain,(
% 0.10/0.42    $false | (~spl2_14 | ~spl2_45)),
% 0.10/0.42    inference(subsumption_resolution,[],[f1531,f1051])).
% 0.10/0.42  fof(f1051,plain,(
% 0.10/0.42    ~r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_45),
% 0.10/0.42    inference(subsumption_resolution,[],[f1050,f32])).
% 0.10/0.42  fof(f32,plain,(
% 0.10/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0))),
% 0.10/0.42    inference(cnf_transformation,[],[f27])).
% 0.10/0.42  fof(f27,plain,(
% 0.10/0.42    (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.10/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26,f25])).
% 0.10/0.42  fof(f25,plain,(
% 0.10/0.42    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f26,plain,(
% 0.10/0.42    ? [X1] : (k2_relat_1(k5_relat_1(sK0,X1)) != k9_relat_1(X1,k2_relat_1(sK0)) & v1_relat_1(X1)) => (k2_relat_1(k5_relat_1(sK0,sK1)) != k9_relat_1(sK1,k2_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.10/0.42    introduced(choice_axiom,[])).
% 0.10/0.42  fof(f14,plain,(
% 0.10/0.42    ? [X0] : (? [X1] : (k2_relat_1(k5_relat_1(X0,X1)) != k9_relat_1(X1,k2_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f13])).
% 0.10/0.42  fof(f13,negated_conjecture,(
% 0.10/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.10/0.42    inference(negated_conjecture,[],[f12])).
% 0.10/0.42  fof(f12,conjecture,(
% 0.10/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.10/0.42  fof(f1050,plain,(
% 0.10/0.42    k2_relat_1(k5_relat_1(sK0,sK1)) = k9_relat_1(sK1,k2_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_45),
% 0.10/0.42    inference(resolution,[],[f1015,f45])).
% 0.10/0.42  fof(f45,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f29])).
% 0.10/0.42  fof(f29,plain,(
% 0.10/0.42    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.10/0.42    inference(flattening,[],[f28])).
% 0.10/0.42  fof(f28,plain,(
% 0.10/0.42    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.10/0.42    inference(nnf_transformation,[],[f1])).
% 0.10/0.42  fof(f1,axiom,(
% 0.10/0.42    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.10/0.42  fof(f1015,plain,(
% 0.10/0.42    r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))) | ~spl2_45),
% 0.10/0.42    inference(avatar_component_clause,[],[f1013])).
% 0.10/0.42  fof(f1013,plain,(
% 0.10/0.42    spl2_45 <=> r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0)))),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.10/0.42  fof(f1531,plain,(
% 0.10/0.42    r1_tarski(k9_relat_1(sK1,k2_relat_1(sK0)),k2_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_14),
% 0.10/0.42    inference(superposition,[],[f1482,f53])).
% 0.10/0.42  fof(f53,plain,(
% 0.10/0.42    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.10/0.42    inference(resolution,[],[f30,f34])).
% 0.10/0.42  fof(f34,plain,(
% 0.10/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f15])).
% 0.10/0.42  fof(f15,plain,(
% 0.10/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f5])).
% 0.10/0.42  fof(f5,axiom,(
% 0.10/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.10/0.42  fof(f30,plain,(
% 0.10/0.42    v1_relat_1(sK0)),
% 0.10/0.42    inference(cnf_transformation,[],[f27])).
% 0.10/0.42  fof(f1482,plain,(
% 0.10/0.42    ( ! [X1] : (r1_tarski(k9_relat_1(sK1,k9_relat_1(sK0,X1)),k2_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl2_14),
% 0.10/0.42    inference(backward_demodulation,[],[f792,f1224])).
% 0.10/0.42  fof(f1224,plain,(
% 0.10/0.42    ( ! [X3] : (k9_relat_1(sK1,k9_relat_1(sK0,X3)) = k2_relat_1(k5_relat_1(k7_relat_1(sK0,X3),sK1))) ) | ~spl2_14),
% 0.10/0.42    inference(forward_demodulation,[],[f330,f1222])).
% 0.10/0.42  fof(f1222,plain,(
% 0.10/0.42    ( ! [X2] : (k5_relat_1(k7_relat_1(sK0,X2),sK1) = k7_relat_1(k5_relat_1(sK0,sK1),X2)) ) | ~spl2_14),
% 0.10/0.42    inference(forward_demodulation,[],[f317,f200])).
% 0.10/0.42  fof(f200,plain,(
% 0.10/0.42    ( ! [X2] : (k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) = k5_relat_1(k7_relat_1(sK0,X2),sK1)) )),
% 0.10/0.42    inference(forward_demodulation,[],[f195,f50])).
% 0.10/0.42  fof(f50,plain,(
% 0.10/0.42    ( ! [X3] : (k7_relat_1(sK0,X3) = k5_relat_1(k6_relat_1(X3),sK0)) )),
% 0.10/0.42    inference(resolution,[],[f30,f39])).
% 0.10/0.42  fof(f39,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f20])).
% 0.10/0.42  fof(f20,plain,(
% 0.10/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f11])).
% 0.10/0.42  fof(f11,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.10/0.42  fof(f195,plain,(
% 0.10/0.42    ( ! [X2] : (k5_relat_1(k5_relat_1(k6_relat_1(X2),sK0),sK1) = k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1))) )),
% 0.10/0.42    inference(resolution,[],[f131,f33])).
% 0.10/0.42  fof(f33,plain,(
% 0.10/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.10/0.42    inference(cnf_transformation,[],[f3])).
% 0.10/0.42  fof(f3,axiom,(
% 0.10/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.10/0.42  fof(f131,plain,(
% 0.10/0.42    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(k5_relat_1(X8,sK0),sK1) = k5_relat_1(X8,k5_relat_1(sK0,sK1))) )),
% 0.10/0.42    inference(resolution,[],[f57,f30])).
% 0.10/0.42  fof(f57,plain,(
% 0.10/0.42    ( ! [X4,X5] : (~v1_relat_1(X5) | k5_relat_1(k5_relat_1(X4,X5),sK1) = k5_relat_1(X4,k5_relat_1(X5,sK1)) | ~v1_relat_1(X4)) )),
% 0.10/0.42    inference(resolution,[],[f31,f37])).
% 0.10/0.42  fof(f37,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f18])).
% 0.10/0.42  fof(f18,plain,(
% 0.10/0.42    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f9])).
% 0.10/0.42  fof(f9,axiom,(
% 0.10/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.10/0.42  fof(f31,plain,(
% 0.10/0.42    v1_relat_1(sK1)),
% 0.10/0.42    inference(cnf_transformation,[],[f27])).
% 0.10/0.42  fof(f317,plain,(
% 0.10/0.42    ( ! [X2] : (k5_relat_1(k6_relat_1(X2),k5_relat_1(sK0,sK1)) = k7_relat_1(k5_relat_1(sK0,sK1),X2)) ) | ~spl2_14),
% 0.10/0.42    inference(resolution,[],[f289,f39])).
% 0.10/0.42  fof(f289,plain,(
% 0.10/0.42    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_14),
% 0.10/0.42    inference(avatar_component_clause,[],[f288])).
% 0.10/0.42  fof(f288,plain,(
% 0.10/0.42    spl2_14 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.10/0.42  fof(f330,plain,(
% 0.10/0.42    ( ! [X3] : (k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X3)) = k9_relat_1(sK1,k9_relat_1(sK0,X3))) ) | ~spl2_14),
% 0.10/0.42    inference(forward_demodulation,[],[f318,f114])).
% 0.10/0.42  fof(f114,plain,(
% 0.10/0.42    ( ! [X8] : (k9_relat_1(k5_relat_1(sK0,sK1),X8) = k9_relat_1(sK1,k9_relat_1(sK0,X8))) )),
% 0.10/0.42    inference(resolution,[],[f54,f30])).
% 0.10/0.42  fof(f54,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k5_relat_1(X0,sK1),X1) = k9_relat_1(sK1,k9_relat_1(X0,X1))) )),
% 0.10/0.42    inference(resolution,[],[f31,f41])).
% 0.10/0.42  fof(f41,plain,(
% 0.10/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f22])).
% 0.10/0.42  fof(f22,plain,(
% 0.10/0.42    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f7])).
% 0.10/0.42  fof(f7,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.10/0.42  fof(f318,plain,(
% 0.10/0.42    ( ! [X3] : (k2_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),X3)) = k9_relat_1(k5_relat_1(sK0,sK1),X3)) ) | ~spl2_14),
% 0.10/0.42    inference(resolution,[],[f289,f40])).
% 0.10/0.42  fof(f40,plain,(
% 0.10/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f21])).
% 0.10/0.42  fof(f21,plain,(
% 0.10/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.10/0.42    inference(ennf_transformation,[],[f6])).
% 0.10/0.42  fof(f6,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.10/0.42  fof(f792,plain,(
% 0.10/0.42    ( ! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl2_14),
% 0.10/0.42    inference(subsumption_resolution,[],[f791,f33])).
% 0.10/0.42  fof(f791,plain,(
% 0.10/0.42    ( ! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(k6_relat_1(X1))) ) | ~spl2_14),
% 0.10/0.42    inference(subsumption_resolution,[],[f788,f289])).
% 0.10/0.42  fof(f788,plain,(
% 0.10/0.42    ( ! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(k7_relat_1(sK0,X1),sK1)),k2_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(k5_relat_1(sK0,sK1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.10/0.42    inference(superposition,[],[f36,f200])).
% 0.10/0.42  fof(f36,plain,(
% 0.10/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f17])).
% 0.10/0.42  fof(f17,plain,(
% 0.10/0.42    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f8])).
% 0.10/0.42  fof(f8,axiom,(
% 0.10/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.10/0.42  fof(f1022,plain,(
% 0.10/0.42    spl2_44),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f1021])).
% 0.10/0.42  fof(f1021,plain,(
% 0.10/0.42    $false | spl2_44),
% 0.10/0.42    inference(subsumption_resolution,[],[f1020,f31])).
% 0.10/0.42  fof(f1020,plain,(
% 0.10/0.42    ~v1_relat_1(sK1) | spl2_44),
% 0.10/0.42    inference(resolution,[],[f1011,f38])).
% 0.10/0.42  fof(f38,plain,(
% 0.10/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f19])).
% 0.10/0.42  fof(f19,plain,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f4])).
% 0.10/0.42  fof(f4,axiom,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.10/0.42  fof(f1011,plain,(
% 0.10/0.42    ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) | spl2_44),
% 0.10/0.42    inference(avatar_component_clause,[],[f1009])).
% 0.10/0.42  fof(f1009,plain,(
% 0.10/0.42    spl2_44 <=> v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.10/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.10/0.42  fof(f1019,plain,(
% 0.10/0.42    ~spl2_44 | spl2_45),
% 0.10/0.42    inference(avatar_split_clause,[],[f1018,f1013,f1009])).
% 0.10/0.42  fof(f1018,plain,(
% 0.10/0.42    r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k9_relat_1(sK1,k2_relat_1(sK0))) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.10/0.42    inference(forward_demodulation,[],[f1017,f55])).
% 0.10/0.42  fof(f55,plain,(
% 0.10/0.42    ( ! [X2] : (k2_relat_1(k7_relat_1(sK1,X2)) = k9_relat_1(sK1,X2)) )),
% 0.10/0.42    inference(resolution,[],[f31,f40])).
% 0.10/0.42  fof(f1017,plain,(
% 0.10/0.42    r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.10/0.42    inference(subsumption_resolution,[],[f1006,f30])).
% 0.10/0.42  fof(f1006,plain,(
% 0.10/0.42    r1_tarski(k2_relat_1(k5_relat_1(sK0,sK1)),k2_relat_1(k7_relat_1(sK1,k2_relat_1(sK0)))) | ~v1_relat_1(k7_relat_1(sK1,k2_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.10/0.42    inference(superposition,[],[f36,f955])).
% 0.10/0.42  fof(f955,plain,(
% 0.10/0.42    k5_relat_1(sK0,sK1) = k5_relat_1(sK0,k7_relat_1(sK1,k2_relat_1(sK0)))),
% 0.10/0.42    inference(superposition,[],[f312,f52])).
% 0.10/0.42  fof(f52,plain,(
% 0.10/0.42    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.10/0.42    inference(resolution,[],[f30,f35])).
% 0.10/0.42  fof(f35,plain,(
% 0.10/0.42    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.10/0.42    inference(cnf_transformation,[],[f16])).
% 0.10/0.42  fof(f16,plain,(
% 0.10/0.42    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.10/0.42    inference(ennf_transformation,[],[f10])).
% 0.10/0.42  fof(f10,axiom,(
% 0.10/0.42    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.10/0.42  fof(f312,plain,(
% 0.10/0.42    ( ! [X11] : (k5_relat_1(k5_relat_1(sK0,k6_relat_1(X11)),sK1) = k5_relat_1(sK0,k7_relat_1(sK1,X11))) )),
% 0.10/0.42    inference(resolution,[],[f133,f30])).
% 0.10/0.42  fof(f133,plain,(
% 0.10/0.42    ( ! [X4,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k7_relat_1(sK1,X4))) )),
% 0.10/0.42    inference(forward_demodulation,[],[f129,f56])).
% 0.10/0.42  fof(f56,plain,(
% 0.10/0.42    ( ! [X3] : (k7_relat_1(sK1,X3) = k5_relat_1(k6_relat_1(X3),sK1)) )),
% 0.10/0.42    inference(resolution,[],[f31,f39])).
% 0.10/0.42  fof(f129,plain,(
% 0.10/0.42    ( ! [X4,X3] : (k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),sK1) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK1)) | ~v1_relat_1(X3)) )),
% 0.10/0.42    inference(resolution,[],[f57,f33])).
% 0.10/0.42  fof(f305,plain,(
% 0.10/0.42    spl2_14),
% 0.10/0.42    inference(avatar_contradiction_clause,[],[f304])).
% 0.10/0.42  fof(f304,plain,(
% 0.10/0.42    $false | spl2_14),
% 0.10/0.42    inference(subsumption_resolution,[],[f303,f30])).
% 0.10/0.42  fof(f303,plain,(
% 0.10/0.42    ~v1_relat_1(sK0) | spl2_14),
% 0.10/0.42    inference(subsumption_resolution,[],[f302,f31])).
% 0.10/0.42  fof(f302,plain,(
% 0.10/0.42    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl2_14),
% 0.10/0.42    inference(resolution,[],[f290,f42])).
% 0.10/0.42  fof(f42,plain,(
% 0.10/0.42    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.10/0.42    inference(cnf_transformation,[],[f24])).
% 0.10/0.42  fof(f24,plain,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.10/0.42    inference(flattening,[],[f23])).
% 0.10/0.42  fof(f23,plain,(
% 0.10/0.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.10/0.42    inference(ennf_transformation,[],[f2])).
% 0.10/0.42  fof(f2,axiom,(
% 0.10/0.42    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.10/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.10/0.42  fof(f290,plain,(
% 0.10/0.42    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl2_14),
% 0.10/0.42    inference(avatar_component_clause,[],[f288])).
% 0.10/0.42  % SZS output end Proof for theBenchmark
% 0.10/0.42  % (10408)------------------------------
% 0.10/0.42  % (10408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.10/0.42  % (10408)Termination reason: Refutation
% 0.10/0.42  
% 0.10/0.42  % (10408)Memory used [KB]: 11769
% 0.10/0.42  % (10408)Time elapsed: 0.129 s
% 0.10/0.42  % (10408)------------------------------
% 0.10/0.42  % (10408)------------------------------
% 0.10/0.42  % (10405)Success in time 0.16 s
%------------------------------------------------------------------------------

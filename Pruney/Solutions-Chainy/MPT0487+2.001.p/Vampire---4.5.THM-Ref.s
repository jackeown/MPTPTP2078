%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 296 expanded)
%              Number of leaves         :   15 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  231 (1917 expanded)
%              Number of equality atoms :   76 ( 856 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f267,f278])).

fof(f278,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f276,f35])).

fof(f35,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != sK3
    & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X1 != X3
                & k6_relat_1(X0) = k5_relat_1(X2,X3)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                & r1_tarski(k2_relat_1(X1),X0)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != X3
              & k5_relat_1(X2,X3) = k6_relat_1(sK0)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
              & r1_tarski(k2_relat_1(sK1),sK0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != X3
            & k5_relat_1(X2,X3) = k6_relat_1(sK0)
            & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
            & r1_tarski(k2_relat_1(sK1),sK0)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK1 != X3
          & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
          & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
          & r1_tarski(k2_relat_1(sK1),sK0)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( sK1 != X3
        & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
        & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
        & r1_tarski(k2_relat_1(sK1),sK0)
        & v1_relat_1(X3) )
   => ( sK1 != sK3
      & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
      & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).

fof(f276,plain,
    ( sK1 = sK3
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f258,f269])).

fof(f269,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(sK0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f54,f84])).

fof(f84,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_2
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f258,plain,(
    sK3 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f257,f69])).

fof(f69,plain,(
    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f257,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f254,f33])).

fof(f33,plain,(
    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f254,plain,(
    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(resolution,[],[f209,f29])).

fof(f209,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k6_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f207,f34])).

fof(f34,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f207,plain,(
    ! [X1] :
      ( k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),sK3) = k5_relat_1(X0,k5_relat_1(X1,sK3))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f267,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f266,f78])).

fof(f78,plain,
    ( spl4_1
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f266,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f265,f31])).

fof(f265,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f139,f261])).

fof(f261,plain,(
    r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f55,f258])).

fof(f55,plain,(
    ! [X2] : r1_tarski(k5_relat_1(sK1,k6_relat_1(X2)),sK1) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f139,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ r1_tarski(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f58,f110])).

fof(f110,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f109,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f109,plain,(
    k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f108,f34])).

fof(f108,plain,(
    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f107,f31])).

fof(f107,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f105,f30])).

fof(f105,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f104,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f104,plain,(
    r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f103,f44])).

fof(f103,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK3))),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f29])).

fof(f102,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK3))),k2_relat_1(sK2))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f67,f33])).

fof(f67,plain,(
    ! [X6] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X6,sK2)),k2_relat_1(sK2))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f58,plain,(
    ! [X5] :
      ( r1_tarski(k2_relat_1(X5),k2_relat_1(sK1))
      | ~ r1_tarski(X5,sK1)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f85,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f76,f82,f78])).

fof(f76,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f32,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:47:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (31964)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (31971)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (31963)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (31964)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (31980)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (31979)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (31972)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f282,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f85,f267,f278])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    ~spl4_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f277])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    $false | ~spl4_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f276,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    sK1 != sK3),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ((sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25,f24,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) => (sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1] : (? [X2] : (? [X3] : ((X1 != X3 & (k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.21/0.57    inference(negated_conjecture,[],[f10])).
% 0.21/0.57  fof(f10,conjecture,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    sK1 = sK3 | ~spl4_2),
% 0.21/0.57    inference(backward_demodulation,[],[f258,f269])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) | ~spl4_2),
% 0.21/0.57    inference(backward_demodulation,[],[f54,f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | ~spl4_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    spl4_2 <=> sK0 = k2_relat_1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.57    inference(resolution,[],[f29,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    v1_relat_1(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f258,plain,(
% 0.21/0.57    sK3 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f257,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 0.21/0.57    inference(resolution,[],[f31,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    v1_relat_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f254,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f254,plain,(
% 0.21/0.57    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f209,f29])).
% 0.21/0.57  fof(f209,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k6_relat_1(sK0))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f207,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    ( ! [X1] : (k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(resolution,[],[f68,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),sK3) = k5_relat_1(X0,k5_relat_1(X1,sK3)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(resolution,[],[f31,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    spl4_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f266,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    spl4_1 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.57    inference(subsumption_resolution,[],[f265,f31])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    r1_tarski(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f139,f261])).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    r1_tarski(sK3,sK1)),
% 0.21/0.57    inference(superposition,[],[f55,f258])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X2] : (r1_tarski(k5_relat_1(sK1,k6_relat_1(X2)),sK1)) )),
% 0.21/0.57    inference(resolution,[],[f29,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    r1_tarski(sK0,k2_relat_1(sK1)) | ~r1_tarski(sK3,sK1) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(superposition,[],[f58,f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK3)),
% 0.21/0.57    inference(forward_demodulation,[],[f109,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f108,f34])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3))),
% 0.21/0.57    inference(subsumption_resolution,[],[f107,f31])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f105,f30])).
% 0.21/0.57  fof(f105,plain,(
% 0.21/0.57    k2_relat_1(sK3) = k2_relat_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f104,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))),
% 0.21/0.57    inference(forward_demodulation,[],[f103,f44])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK3))),k2_relat_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f102,f29])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(sK3))),k2_relat_1(sK2)) | ~v1_relat_1(sK1)),
% 0.21/0.57    inference(superposition,[],[f67,f33])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X6] : (r1_tarski(k2_relat_1(k5_relat_1(X6,sK2)),k2_relat_1(sK2)) | ~v1_relat_1(X6)) )),
% 0.21/0.57    inference(resolution,[],[f30,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X5] : (r1_tarski(k2_relat_1(X5),k2_relat_1(sK1)) | ~r1_tarski(X5,sK1) | ~v1_relat_1(X5)) )),
% 0.21/0.57    inference(resolution,[],[f29,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ~spl4_1 | spl4_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f76,f82,f78])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK1) | ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.57    inference(resolution,[],[f32,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (31964)------------------------------
% 0.21/0.57  % (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (31964)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (31964)Memory used [KB]: 10746
% 0.21/0.57  % (31964)Time elapsed: 0.112 s
% 0.21/0.57  % (31964)------------------------------
% 0.21/0.57  % (31964)------------------------------
% 0.21/0.57  % (31957)Success in time 0.202 s
%------------------------------------------------------------------------------

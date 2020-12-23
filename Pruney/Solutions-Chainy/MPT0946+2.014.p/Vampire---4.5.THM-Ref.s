%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  153 (1762 expanded)
%              Number of leaves         :   17 ( 467 expanded)
%              Depth                    :   41
%              Number of atoms          :  524 (8209 expanded)
%              Number of equality atoms :  105 (1810 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f811,plain,(
    $false ),
    inference(subsumption_resolution,[],[f810,f48])).

fof(f48,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f810,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f809,f708])).

fof(f708,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f707,f49])).

fof(f49,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f707,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f704,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f704,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f702,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f702,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f650,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f650,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f649,f49])).

fof(f649,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK1,sK0)
    | r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f648,f86])).

fof(f86,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f81,f52])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

% (20389)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f81,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).

% (20408)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f648,plain,
    ( r1_ordinal1(sK1,sK0)
    | r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) ),
    inference(forward_demodulation,[],[f623,f86])).

fof(f623,plain,
    ( r1_ordinal1(k3_relat_1(k1_wellord2(sK1)),sK0)
    | r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(k3_relat_1(k1_wellord2(sK1))) ),
    inference(superposition,[],[f130,f610])).

fof(f610,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f607,f49])).

fof(f607,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f597,f426])).

fof(f426,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | ~ v3_ordinal1(X0)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK0),X0) ) ),
    inference(forward_demodulation,[],[f425,f86])).

fof(f425,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | k1_wellord2(k3_relat_1(k1_wellord2(X0))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k1_wellord2(X0))) ) ),
    inference(forward_demodulation,[],[f421,f86])).

fof(f421,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0)))
      | r2_hidden(sK0,X0)
      | k1_wellord2(k3_relat_1(k1_wellord2(X0))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k1_wellord2(X0))) ) ),
    inference(superposition,[],[f232,f93])).

fof(f93,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f66,f82])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X0),X1)))
      | r2_hidden(sK0,X1)
      | k1_wellord2(k3_relat_1(k2_wellord1(k1_wellord2(X0),X1))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k2_wellord1(k1_wellord2(X0),X1))) ) ),
    inference(resolution,[],[f186,f66])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK0)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))
      | r2_hidden(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,X0)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))
      | r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK0)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) ) ),
    inference(resolution,[],[f122,f94])).

fof(f122,plain,(
    ! [X4,X5] :
      ( r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X5),X4)),sK0)
      | r2_hidden(sK0,X4)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X5),X4))) ) ),
    inference(resolution,[],[f99,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_ordinal1(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2)))
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

% (20407)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f597,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f596,f138])).

fof(f138,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f118,f50])).

fof(f50,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f90,f52])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r4_wellord1(k1_wellord2(X1),X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1)) ) ),
    inference(resolution,[],[f54,f52])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f596,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f595])).

fof(f595,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f286,f336])).

fof(f336,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f330,f66])).

fof(f330,plain,
    ( r1_tarski(sK1,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f328,f82])).

fof(f328,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f293,f72])).

fof(f293,plain,
    ( r2_hidden(sK0,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f289,f49])).

fof(f289,plain,
    ( r2_hidden(sK0,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f278,f238])).

fof(f238,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f237,f86])).

fof(f237,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0)))
      | r2_hidden(sK0,X0) ) ),
    inference(forward_demodulation,[],[f234,f86])).

fof(f234,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k1_wellord2(X0)),sK0)
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0)))
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f186,f93])).

fof(f278,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ) ),
    inference(superposition,[],[f165,f162])).

fof(f162,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f155,f66])).

fof(f155,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f154,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f144,f95])).

fof(f95,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK1)
      | r1_tarski(X1,sK1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f67,f49])).

fof(f144,plain,
    ( r1_ordinal1(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f143,f48])).

fof(f143,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f140,f49])).

fof(f140,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f103,f92])).

% (20398)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f92,plain,(
    ! [X1] :
      ( r2_hidden(sK1,X1)
      | r1_ordinal1(X1,sK1)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f56,f49])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_wellord1(k1_wellord2(sK0),X0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_wellord1(k1_wellord2(sK0),X0))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f102,f157])).

fof(f157,plain,(
    ! [X0] : k1_wellord1(k1_wellord2(sK0),X0) = k3_relat_1(k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0))) ),
    inference(resolution,[],[f106,f48])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) ) ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f58,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2)))
      | r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f101,f86])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2)))
      | r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f286,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f285,f49])).

fof(f285,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f117,f173])).

fof(f173,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f160,f66])).

fof(f160,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f150,f94])).

fof(f150,plain,
    ( r1_ordinal1(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f149,f49])).

fof(f149,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f104,f91])).

fof(f104,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_wellord1(k1_wellord2(sK1),X1) = X1
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f57,f49])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f116,f86])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f53,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f130,plain,(
    ! [X4,X5] :
      ( r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X4),X5)),sK0)
      | r2_hidden(sK0,X4)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X4),X5))) ) ),
    inference(resolution,[],[f102,f91])).

fof(f809,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f805,f51])).

fof(f51,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f805,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f777,f391])).

fof(f391,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | sK1 = X0
      | ~ r1_tarski(sK1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f390,f86])).

fof(f390,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ r1_tarski(sK1,X0)
      | r2_hidden(sK1,X0)
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0))) ) ),
    inference(forward_demodulation,[],[f389,f86])).

fof(f389,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK1,X0)
      | sK1 = k3_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0))) ) ),
    inference(forward_demodulation,[],[f385,f86])).

fof(f385,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k3_relat_1(k1_wellord2(X0)))
      | r2_hidden(sK1,X0)
      | sK1 = k3_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(k3_relat_1(k1_wellord2(X0))) ) ),
    inference(superposition,[],[f249,f93])).

fof(f249,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK1,k3_relat_1(k2_wellord1(k1_wellord2(X2),X3)))
      | r2_hidden(sK1,X3)
      | sK1 = k3_relat_1(k2_wellord1(k1_wellord2(X2),X3))
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X2),X3))) ) ),
    inference(resolution,[],[f195,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK1)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))
      | r2_hidden(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1,X0)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))
      | r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK1)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) ) ),
    inference(resolution,[],[f123,f95])).

fof(f123,plain,(
    ! [X6,X7] :
      ( r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X7),X6)),sK1)
      | r2_hidden(sK1,X6)
      | ~ v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X7),X6))) ) ),
    inference(resolution,[],[f99,f92])).

fof(f777,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f776,f50])).

fof(f776,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(forward_demodulation,[],[f775,f610])).

fof(f775,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f773,f48])).

fof(f773,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(superposition,[],[f117,f715])).

fof(f715,plain,(
    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f708,f164])).

fof(f164,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f163,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f155,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:10:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (20402)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (20386)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (20388)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (20392)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (20390)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (20409)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (20391)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (20402)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (20400)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (20392)Refutation not found, incomplete strategy% (20392)------------------------------
% 0.22/0.53  % (20392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20392)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20392)Memory used [KB]: 10618
% 0.22/0.53  % (20392)Time elapsed: 0.102 s
% 0.22/0.53  % (20392)------------------------------
% 0.22/0.53  % (20392)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f811,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f810,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v3_ordinal1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f38,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.53  fof(f810,plain,(
% 0.22/0.53    ~v3_ordinal1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f809,f708])).
% 0.22/0.53  fof(f708,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f707,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v3_ordinal1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f707,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.53    inference(resolution,[],[f704,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_ordinal1(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f67,f48])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.53  fof(f704,plain,(
% 0.22/0.53    r1_ordinal1(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f702,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f702,plain,(
% 0.22/0.53    r1_ordinal1(sK1,sK0) | ~r1_tarski(sK0,sK0)),
% 0.22/0.53    inference(resolution,[],[f650,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f650,plain,(
% 0.22/0.53    r2_hidden(sK0,sK0) | r1_ordinal1(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f649,f49])).
% 0.22/0.53  fof(f649,plain,(
% 0.22/0.53    ~v3_ordinal1(sK1) | r1_ordinal1(sK1,sK0) | r2_hidden(sK0,sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f648,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f81,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.53  % (20389)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f42,f43])).
% 0.22/0.54  % (20408)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(rectify,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.54  fof(f648,plain,(
% 0.22/0.54    r1_ordinal1(sK1,sK0) | r2_hidden(sK0,sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f623,f86])).
% 0.22/0.54  fof(f623,plain,(
% 0.22/0.54    r1_ordinal1(k3_relat_1(k1_wellord2(sK1)),sK0) | r2_hidden(sK0,sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(sK1)))),
% 0.22/0.54    inference(superposition,[],[f130,f610])).
% 0.22/0.54  fof(f610,plain,(
% 0.22/0.54    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f607,f49])).
% 0.22/0.54  fof(f607,plain,(
% 0.22/0.54    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f603])).
% 0.22/0.54  fof(f603,plain,(
% 0.22/0.54    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f597,f426])).
% 0.22/0.54  fof(f426,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK0),X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f425,f86])).
% 0.22/0.54  fof(f425,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | k1_wellord2(k3_relat_1(k1_wellord2(X0))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f421,f86])).
% 0.22/0.54  fof(f421,plain,(
% 0.22/0.54    ( ! [X0] : (~v3_ordinal1(k3_relat_1(k1_wellord2(X0))) | r2_hidden(sK0,X0) | k1_wellord2(k3_relat_1(k1_wellord2(X0))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.54    inference(superposition,[],[f232,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.22/0.54    inference(resolution,[],[f66,f82])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X0),X1))) | r2_hidden(sK0,X1) | k1_wellord2(k3_relat_1(k2_wellord1(k1_wellord2(X0),X1))) = k2_wellord1(k1_wellord2(sK0),k3_relat_1(k2_wellord1(k1_wellord2(X0),X1)))) )),
% 0.22/0.54    inference(resolution,[],[f186,f66])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK0) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) | r2_hidden(sK0,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK0,X0) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) | r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK0) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))) )),
% 0.22/0.54    inference(resolution,[],[f122,f94])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X4,X5] : (r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X5),X4)),sK0) | r2_hidden(sK0,X4) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X5),X4)))) )),
% 0.22/0.54    inference(resolution,[],[f99,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0,X0) | r1_ordinal1(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f56,f48])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2))) | r2_hidden(X0,X2)) )),
% 0.22/0.54    inference(resolution,[],[f74,f52])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  % (20407)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).
% 0.22/0.54  fof(f597,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f596,f138])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.54    inference(resolution,[],[f118,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) | r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) )),
% 0.22/0.54    inference(resolution,[],[f90,f52])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | r4_wellord1(k1_wellord2(X1),X0) | ~r4_wellord1(X0,k1_wellord2(X1))) )),
% 0.22/0.54    inference(resolution,[],[f54,f52])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.54  fof(f596,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f595])).
% 0.22/0.54  fof(f595,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(superposition,[],[f286,f336])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f330,f66])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f328,f82])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0) | ~r1_tarski(sK0,sK0)),
% 0.22/0.54    inference(resolution,[],[f293,f72])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f289,f49])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.54    inference(resolution,[],[f278,f238])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0,X0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f237,f86])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(X0))) | r2_hidden(sK0,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f234,f86])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k3_relat_1(k1_wellord2(X0)),sK0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(X0))) | r2_hidden(sK0,X0)) )),
% 0.22/0.54    inference(superposition,[],[f186,f93])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)) )),
% 0.22/0.54    inference(superposition,[],[f165,f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.54    inference(resolution,[],[f155,f66])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f154,f48])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(resolution,[],[f144,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_ordinal1(X1,sK1) | r1_tarski(X1,sK1) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f67,f49])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    r1_ordinal1(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f48])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f140,f49])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(resolution,[],[f103,f92])).
% 0.22/0.54  % (20398)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK1,X1) | r1_ordinal1(X1,sK1) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f56,f49])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f57,f48])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_wellord1(k1_wellord2(sK0),X0)) | r2_hidden(X1,sK0)) )),
% 0.22/0.54    inference(superposition,[],[f102,f157])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ( ! [X0] : (k1_wellord1(k1_wellord2(sK0),X0) = k3_relat_1(k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0)))) )),
% 0.22/0.54    inference(resolution,[],[f106,f48])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f105,f52])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X0),X1) = k3_relat_1(k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v1_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f58,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_wellord1(X1) | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2))) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f101,f86])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(k1_wellord2(X1),X2))) | r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))) )),
% 0.22/0.54    inference(resolution,[],[f73,f52])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f285,f49])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(superposition,[],[f117,f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f160,f66])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    r1_tarski(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f159,f49])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.54    inference(resolution,[],[f150,f94])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    r1_ordinal1(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f49])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f146,f48])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~v3_ordinal1(sK0) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.22/0.54    inference(resolution,[],[f104,f91])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_wellord1(k1_wellord2(sK1),X1) = X1 | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f57,f49])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f116,f86])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f115,f52])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f53,f55])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ( ! [X4,X5] : (r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X4),X5)),sK0) | r2_hidden(sK0,X4) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X4),X5)))) )),
% 0.22/0.54    inference(resolution,[],[f102,f91])).
% 0.22/0.54  fof(f809,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f805,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    sK0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f805,plain,(
% 0.22/0.54    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(resolution,[],[f777,f391])).
% 0.22/0.54  fof(f391,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~r1_tarski(sK1,X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f390,f86])).
% 0.22/0.54  fof(f390,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | r2_hidden(sK1,X0) | ~v3_ordinal1(k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f389,f86])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK1,X0) | sK1 = k3_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f385,f86])).
% 0.22/0.54  fof(f385,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(sK1,k3_relat_1(k1_wellord2(X0))) | r2_hidden(sK1,X0) | sK1 = k3_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.54    inference(superposition,[],[f249,f93])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(sK1,k3_relat_1(k2_wellord1(k1_wellord2(X2),X3))) | r2_hidden(sK1,X3) | sK1 = k3_relat_1(k2_wellord1(k1_wellord2(X2),X3)) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X2),X3)))) )),
% 0.22/0.54    inference(resolution,[],[f195,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK1) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) | r2_hidden(sK1,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f191])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK1,X0) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0))) | r1_tarski(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)),sK1) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X1),X0)))) )),
% 0.22/0.54    inference(resolution,[],[f123,f95])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X6,X7] : (r1_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X7),X6)),sK1) | r2_hidden(sK1,X6) | ~v3_ordinal1(k3_relat_1(k2_wellord1(k1_wellord2(X7),X6)))) )),
% 0.22/0.54    inference(resolution,[],[f99,f92])).
% 0.22/0.54  fof(f777,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f776,f50])).
% 0.22/0.54  fof(f776,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f775,f610])).
% 0.22/0.54  fof(f775,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f773,f48])).
% 0.22/0.54  fof(f773,plain,(
% 0.22/0.54    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.22/0.54    inference(superposition,[],[f117,f715])).
% 0.22/0.54  fof(f715,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f708,f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f163,f51])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | ~r1_tarski(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f155,f71])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (20402)------------------------------
% 0.22/0.54  % (20402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20402)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (20402)Memory used [KB]: 1791
% 0.22/0.54  % (20402)Time elapsed: 0.119 s
% 0.22/0.54  % (20402)------------------------------
% 0.22/0.54  % (20402)------------------------------
% 0.22/0.54  % (20385)Success in time 0.176 s
%------------------------------------------------------------------------------

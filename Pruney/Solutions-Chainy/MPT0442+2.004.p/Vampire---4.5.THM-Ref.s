%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 113 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 487 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f71])).

% (26669)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f71,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f28,f70])).

fof(f70,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(X0,k2_relat_1(sK1)),k2_relat_1(sK0))
      | r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f15,f14,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (26655)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK8(X1,k2_relat_1(sK1))),sK0)
      | r1_tarski(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
        & r1_tarski(X0,X1) )
   => ( ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
        | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
          & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

% (26653)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f56,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X5,X3)
      | ~ r2_hidden(k4_tarski(X4,sK8(X2,k2_relat_1(X3))),X5)
      | r1_tarski(X2,k2_relat_1(X3)) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK8(X1,k2_relat_1(X2))),X2)
      | r1_tarski(X1,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f78,f38])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(X0,k1_relat_1(sK1)),k1_relat_1(sK0))
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,k1_relat_1(sK1)),X1),sK0)
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f60,f27])).

fof(f60,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X5,X3)
      | ~ r2_hidden(k4_tarski(sK8(X2,k1_relat_1(X3)),X4),X5)
      | r1_tarski(X2,k1_relat_1(X3)) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK8(X0,k1_relat_1(X1)),X2),X1)
      | r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:03:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (26662)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (26654)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (26654)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f83,f71])).
% 0.22/0.51  % (26669)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f28,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f65,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK8(X0,k2_relat_1(sK1)),k2_relat_1(sK0)) | r1_tarski(X0,k2_relat_1(sK1))) )),
% 0.22/0.51    inference(resolution,[],[f63,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f15,f14,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.52  % (26655)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.52    inference(rectify,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK8(X1,k2_relat_1(sK1))),sK0) | r1_tarski(X1,k2_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f56,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    (~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) & r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1)) => ((~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) & r1_tarski(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1] : ((~r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) & r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.52  % (26653)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X4,X2,X5,X3] : (~r1_tarski(X5,X3) | ~r2_hidden(k4_tarski(X4,sK8(X2,k2_relat_1(X3))),X5) | r1_tarski(X2,k2_relat_1(X3))) )),
% 0.22/0.52    inference(resolution,[],[f47,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,sK8(X1,k2_relat_1(X2))),X2) | r1_tarski(X1,k2_relat_1(X2))) )),
% 0.22/0.52    inference(resolution,[],[f40,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.22/0.52    inference(resolution,[],[f78,f38])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK8(X0,k1_relat_1(sK1)),k1_relat_1(sK0)) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f75,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.22/0.52    inference(equality_resolution,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f18,f21,f20,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.52    inference(rectify,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK8(X0,k1_relat_1(sK1)),X1),sK0) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f60,f27])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X4,X2,X5,X3] : (~r1_tarski(X5,X3) | ~r2_hidden(k4_tarski(sK8(X2,k1_relat_1(X3)),X4),X5) | r1_tarski(X2,k1_relat_1(X3))) )),
% 0.22/0.52    inference(resolution,[],[f48,f37])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(sK8(X0,k1_relat_1(X1)),X2),X1) | r1_tarski(X0,k1_relat_1(X1))) )),
% 0.22/0.52    inference(resolution,[],[f42,f39])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (26654)------------------------------
% 0.22/0.52  % (26654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26654)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (26654)Memory used [KB]: 6268
% 0.22/0.52  % (26654)Time elapsed: 0.099 s
% 0.22/0.52  % (26654)------------------------------
% 0.22/0.52  % (26654)------------------------------
% 0.22/0.52  % (26648)Success in time 0.157 s
%------------------------------------------------------------------------------

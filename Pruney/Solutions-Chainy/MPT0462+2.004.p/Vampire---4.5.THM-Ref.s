%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 113 expanded)
%              Number of leaves         :    8 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 796 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f43,plain,(
    r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)) ),
    inference(resolution,[],[f40,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                    & r1_tarski(X2,X3)
                    & r1_tarski(X0,X1)
                    & v1_relat_1(X3) )
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(sK0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3))
                & r1_tarski(X2,X3)
                & r1_tarski(sK0,X1)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
              & r1_tarski(X2,X3)
              & r1_tarski(sK0,sK1)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3))
            & r1_tarski(X2,X3)
            & r1_tarski(sK0,sK1)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
          & r1_tarski(sK2,X3)
          & r1_tarski(sK0,sK1)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3))
        & r1_tarski(sK2,X3)
        & r1_tarski(sK0,sK1)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  & r1_tarski(X2,X3)
                  & r1_tarski(X0,X1)
                  & v1_relat_1(X3) )
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ! [X3] :
                    ( v1_relat_1(X3)
                   => ( ( r1_tarski(X2,X3)
                        & r1_tarski(X0,X1) )
                     => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(f40,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3)) ) ),
    inference(subsumption_resolution,[],[f39,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X1] :
      ( r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f22,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X1] :
      ( r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f74,plain,(
    ~ r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3)) ),
    inference(resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_relat_1(sK0,sK2),X0)
      | ~ r1_tarski(X0,k5_relat_1(sK1,sK3)) ) ),
    inference(resolution,[],[f28,f25])).

fof(f25,plain,(
    ~ r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f70,plain,(
    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f69,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f64,f23])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

% (14111)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f64,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(sK1,sK2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f59,f20])).

fof(f59,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | r1_tarski(k5_relat_1(X4,sK2),k5_relat_1(X5,sK2))
      | ~ r1_tarski(X4,X5)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (14098)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.46  % (14109)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.47  % (14116)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (14105)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (14098)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    inference(resolution,[],[f40,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    (((~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f17,f16,f15,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(sK0,X2),k5_relat_1(sK1,X3)) & r1_tarski(X2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X3] : (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,X3)) & r1_tarski(sK2,X3) & r1_tarski(sK0,sK1) & v1_relat_1(X3)) => (~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1) & v1_relat_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3)) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X1,sK3)) | ~v1_relat_1(X1) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f26,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~r1_tarski(k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    inference(resolution,[],[f70,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k5_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k5_relat_1(sK1,sK3))) )),
% 0.21/0.48    inference(resolution,[],[f28,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2))),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    r1_tarski(k5_relat_1(sK0,sK2),k5_relat_1(sK1,sK2)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f64,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % (14111)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(sK1,sK2)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f59,f20])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~v1_relat_1(X5) | r1_tarski(k5_relat_1(X4,sK2),k5_relat_1(X5,sK2)) | ~r1_tarski(X4,X5) | ~v1_relat_1(X4)) )),
% 0.21/0.48    inference(resolution,[],[f27,f21])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14098)------------------------------
% 0.21/0.48  % (14098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14098)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14098)Memory used [KB]: 5373
% 0.21/0.48  % (14098)Time elapsed: 0.063 s
% 0.21/0.48  % (14098)------------------------------
% 0.21/0.48  % (14098)------------------------------
% 0.21/0.48  % (14117)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (14097)Success in time 0.128 s
%------------------------------------------------------------------------------

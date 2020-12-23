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
% DateTime   : Thu Dec  3 12:56:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 242 expanded)
%              Number of leaves         :    9 ( 106 expanded)
%              Depth                    :   28
%              Number of atoms          :  280 (2209 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ! [X4] :
        ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
        | ~ r2_hidden(X4,k3_relat_1(sK1)) )
    & r2_hidden(sK3,k3_relat_1(sK0))
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                        | ~ r2_hidden(X4,k3_relat_1(X1)) )
                    & r2_hidden(X3,k3_relat_1(X0)) )
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(sK0)) )
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                    | ~ r2_hidden(X4,k3_relat_1(X1)) )
                & r2_hidden(X3,k3_relat_1(sK0)) )
            & r3_wellord1(sK0,X1,X2)
            & v2_wellord1(sK0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
                  | ~ r2_hidden(X4,k3_relat_1(sK1)) )
              & r2_hidden(X3,k3_relat_1(sK0)) )
          & r3_wellord1(sK0,sK1,X2)
          & v2_wellord1(sK0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (8680)Termination reason: Refutation not found, incomplete strategy

% (8680)Memory used [KB]: 10490
% (8680)Time elapsed: 0.084 s
% (8680)------------------------------
% (8680)------------------------------
% (8678)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (8691)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% (8695)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (8695)Refutation not found, incomplete strategy% (8695)------------------------------
% (8695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8695)Termination reason: Refutation not found, incomplete strategy

% (8695)Memory used [KB]: 1535
% (8685)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (8695)Time elapsed: 0.002 s
% (8695)------------------------------
% (8695)------------------------------
% (8693)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (8685)Refutation not found, incomplete strategy% (8685)------------------------------
% (8685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8685)Termination reason: Refutation not found, incomplete strategy

% (8685)Memory used [KB]: 10490
% (8685)Time elapsed: 0.105 s
% (8685)------------------------------
% (8685)------------------------------
% (8701)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(sK1)) )
            & r2_hidden(X3,k3_relat_1(sK0)) )
        & r3_wellord1(sK0,sK1,X2)
        & v2_wellord1(sK0)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
              | ~ r2_hidden(X4,k3_relat_1(sK1)) )
          & r2_hidden(X3,k3_relat_1(sK0)) )
      & r3_wellord1(sK0,sK1,sK2)
      & v2_wellord1(sK0)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (8689)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f16,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
            | ~ r2_hidden(X4,k3_relat_1(sK1)) )
        & r2_hidden(X3,k3_relat_1(sK0)) )
   => ( ! [X4] :
          ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
          | ~ r2_hidden(X4,k3_relat_1(sK1)) )
      & r2_hidden(sK3,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
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
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => ! [X3] :
                      ~ ( ! [X4] :
                            ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                              & r2_hidden(X4,k3_relat_1(X1)) )
                        & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

fof(f58,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f57,plain,(
    ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f53,f23])).

fof(f23,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f24,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f25,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( r3_wellord1(X1,X2,X3)
                  & r1_tarski(X0,k3_relat_1(X1))
                  & v2_wellord1(X1) )
               => ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                  & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

fof(f50,plain,(
    ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    inference(subsumption_resolution,[],[f49,f20])).

fof(f49,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f48,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f47,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f45,f25])).

fof(f45,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f26,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ r2_hidden(sK3,k3_relat_1(sK0))
    | ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
                    & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
          & r2_hidden(X4,k3_relat_1(X1)) )
     => ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
        & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

fof(f41,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1))
    | ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    inference(superposition,[],[f27,f38])).

fof(f38,plain,(
    k9_relat_1(sK2,k1_wellord1(sK0,sK3)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f37,f26])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X1,X2,sK2)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ r3_wellord1(X1,X2,sK2)
      | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8697)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (8690)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (8681)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (8683)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (8687)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (8682)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (8677)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (8680)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (8680)Refutation not found, incomplete strategy% (8680)------------------------------
% 0.21/0.50  % (8680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8679)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (8688)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (8702)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (8688)Refutation not found, incomplete strategy% (8688)------------------------------
% 0.21/0.51  % (8688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8688)Memory used [KB]: 10490
% 0.21/0.51  % (8688)Time elapsed: 0.002 s
% 0.21/0.51  % (8688)------------------------------
% 0.21/0.51  % (8688)------------------------------
% 0.21/0.51  % (8698)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (8702)Refutation not found, incomplete strategy% (8702)------------------------------
% 0.21/0.51  % (8702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8702)Memory used [KB]: 10618
% 0.21/0.51  % (8702)Time elapsed: 0.053 s
% 0.21/0.51  % (8702)------------------------------
% 0.21/0.51  % (8702)------------------------------
% 0.21/0.51  % (8696)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (8698)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (8694)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    (((! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(sK3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,sK2) & v2_wellord1(sK0) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,X1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,X1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (8680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8680)Memory used [KB]: 10490
% 0.21/0.51  % (8680)Time elapsed: 0.084 s
% 0.21/0.51  % (8680)------------------------------
% 0.21/0.51  % (8680)------------------------------
% 0.21/0.51  % (8678)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (8691)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (8695)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (8695)Refutation not found, incomplete strategy% (8695)------------------------------
% 0.21/0.51  % (8695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8695)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8695)Memory used [KB]: 1535
% 0.21/0.51  % (8685)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (8695)Time elapsed: 0.002 s
% 0.21/0.51  % (8695)------------------------------
% 0.21/0.51  % (8695)------------------------------
% 0.21/0.51  % (8693)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (8685)Refutation not found, incomplete strategy% (8685)------------------------------
% 0.21/0.52  % (8685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8685)Memory used [KB]: 10490
% 0.21/0.52  % (8685)Time elapsed: 0.105 s
% 0.21/0.52  % (8685)------------------------------
% 0.21/0.52  % (8685)------------------------------
% 0.21/0.52  % (8701)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,sK2) & v2_wellord1(sK0) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (8689)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) => (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(sK3,k3_relat_1(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f57,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f20])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v2_wellord1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f51,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    r3_wellord1(sK0,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~r3_wellord1(sK0,sK1,sK2) | ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f50,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (! [X3] : ((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (! [X3] : (((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | (~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((r3_wellord1(X1,X2,X3) & r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f20])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f48,f21])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f47,f22])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f23])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f25])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~r3_wellord1(sK0,sK1,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f44,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    r2_hidden(sK3,k3_relat_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) | ~r2_hidden(sK3,k3_relat_1(sK0)) | ~r3_wellord1(sK0,sK1,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.52    inference(resolution,[],[f41,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) => (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3] : ~(! [X4] : ~(k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1)) | ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),
% 0.21/0.52    inference(superposition,[],[f27,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k9_relat_1(sK2,k1_wellord1(sK0,sK3)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3))),
% 0.21/0.52    inference(resolution,[],[f37,f26])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f36,f20])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f35,f21])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.52    inference(resolution,[],[f34,f25])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r3_wellord1(X1,X2,sK2) | ~r2_hidden(X0,k3_relat_1(X1)) | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f33,f22])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(X1)) | ~r3_wellord1(X1,X2,sK2) | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f29,f23])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8698)------------------------------
% 0.21/0.52  % (8698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8698)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8698)Memory used [KB]: 6140
% 0.21/0.52  % (8698)Time elapsed: 0.098 s
% 0.21/0.52  % (8698)------------------------------
% 0.21/0.52  % (8698)------------------------------
% 0.21/0.52  % (8672)Success in time 0.159 s
%------------------------------------------------------------------------------

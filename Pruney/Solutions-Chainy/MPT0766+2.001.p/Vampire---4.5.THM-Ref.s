%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  98 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 ( 934 expanded)
%              Number of equality atoms :   12 (  84 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f23])).

fof(f23,plain,(
    r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
          & sK1 != sK2(X2)
          & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
          & r2_hidden(sK2(X2),k3_relat_1(sK0)) )
        | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
        | ~ r2_hidden(X2,k3_relat_1(sK0)) )
    & ~ r2_hidden(k4_tarski(sK3,sK1),sK0)
    & r2_hidden(sK3,k3_relat_1(sK0))
    & r2_hidden(sK1,k3_relat_1(sK0))
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f13,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & X1 != X3
                    & r2_hidden(k4_tarski(X1,X3),X0)
                    & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X1,X2),X0)
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & ? [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                & r2_hidden(X4,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK0)
                  & r2_hidden(X3,k3_relat_1(sK0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK0)
              | ~ r2_hidden(X2,k3_relat_1(sK0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK0)
              & r2_hidden(X4,k3_relat_1(sK0)) )
          & r2_hidden(X1,k3_relat_1(sK0)) )
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                & X1 != X3
                & r2_hidden(k4_tarski(X1,X3),sK0)
                & r2_hidden(X3,k3_relat_1(sK0)) )
            | ~ r2_hidden(k4_tarski(X1,X2),sK0)
            | ~ r2_hidden(X2,k3_relat_1(sK0)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),sK0)
            & r2_hidden(X4,k3_relat_1(sK0)) )
        & r2_hidden(X1,k3_relat_1(sK0)) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
              & sK1 != X3
              & r2_hidden(k4_tarski(sK1,X3),sK0)
              & r2_hidden(X3,k3_relat_1(sK0)) )
          | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
          | ~ r2_hidden(X2,k3_relat_1(sK0)) )
      & ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,sK1),sK0)
          & r2_hidden(X4,k3_relat_1(sK0)) )
      & r2_hidden(sK1,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
          & sK1 != X3
          & r2_hidden(k4_tarski(sK1,X3),sK0)
          & r2_hidden(X3,k3_relat_1(sK0)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
        & sK1 != sK2(X2)
        & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
        & r2_hidden(sK2(X2),k3_relat_1(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X4] :
        ( ~ r2_hidden(k4_tarski(X4,sK1),sK0)
        & r2_hidden(X4,k3_relat_1(sK0)) )
   => ( ~ r2_hidden(k4_tarski(sK3,sK1),sK0)
      & r2_hidden(sK3,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).

fof(f73,plain,(
    ~ r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f72,f60])).

fof(f60,plain,(
    r2_hidden(k4_tarski(sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f58,f48])).

fof(f48,plain,(
    v1_relat_2(sK0) ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f22,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,
    ( v1_relat_2(sK0)
    | ~ v2_wellord1(sK0) ),
    inference(resolution,[],[f21,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f58,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ v1_relat_2(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK4(X0)),X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK4(X0)),X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK1,sK2(X2)),sK0)
      | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
      | ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (609)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (609)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (607)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (612)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (613)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    r2_hidden(sK1,k3_relat_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    (! [X2] : ((~r2_hidden(k4_tarski(X2,sK2(X2)),sK0) & sK1 != sK2(X2) & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0) & r2_hidden(sK2(X2),k3_relat_1(sK0))) | ~r2_hidden(k4_tarski(sK1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) & (~r2_hidden(k4_tarski(sK3,sK1),sK0) & r2_hidden(sK3,k3_relat_1(sK0))) & r2_hidden(sK1,k3_relat_1(sK0))) & v2_wellord1(sK0) & v1_relat_1(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f13,f12,f11,f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) & r2_hidden(X4,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0))) & v2_wellord1(X0) & v1_relat_1(X0)) => (? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),sK0) & r2_hidden(X3,k3_relat_1(sK0))) | ~r2_hidden(k4_tarski(X1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),sK0) & r2_hidden(X4,k3_relat_1(sK0))) & r2_hidden(X1,k3_relat_1(sK0))) & v2_wellord1(sK0) & v1_relat_1(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),sK0) & r2_hidden(X3,k3_relat_1(sK0))) | ~r2_hidden(k4_tarski(X1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),sK0) & r2_hidden(X4,k3_relat_1(sK0))) & r2_hidden(X1,k3_relat_1(sK0))) => (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) & sK1 != X3 & r2_hidden(k4_tarski(sK1,X3),sK0) & r2_hidden(X3,k3_relat_1(sK0))) | ~r2_hidden(k4_tarski(sK1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,sK1),sK0) & r2_hidden(X4,k3_relat_1(sK0))) & r2_hidden(sK1,k3_relat_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) & sK1 != X3 & r2_hidden(k4_tarski(sK1,X3),sK0) & r2_hidden(X3,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(X2,sK2(X2)),sK0) & sK1 != sK2(X2) & r2_hidden(k4_tarski(sK1,sK2(X2)),sK0) & r2_hidden(sK2(X2),k3_relat_1(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X4] : (~r2_hidden(k4_tarski(X4,sK1),sK0) & r2_hidden(X4,k3_relat_1(sK0))) => (~r2_hidden(k4_tarski(sK3,sK1),sK0) & r2_hidden(sK3,k3_relat_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) & r2_hidden(X4,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0))) & v2_wellord1(X0) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : ((? [X1] : (! [X2] : (? [X3] : (~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X1,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) & r2_hidden(X4,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0))) & v2_wellord1(X0)) & v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : ~(~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) & r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) & ? [X4] : (~r2_hidden(k4_tarski(X4,X1),X0) & r2_hidden(X4,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.50    inference(rectify,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : ~(~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) & r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) & ? [X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(X2,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : ~(~r2_hidden(k4_tarski(X2,X3),X0) & X1 != X3 & r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(X3,k3_relat_1(X0))) & r2_hidden(k4_tarski(X1,X2),X0) & r2_hidden(X2,k3_relat_1(X0))) & ? [X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(X2,k3_relat_1(X0))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k3_relat_1(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK1,sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f59,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_relat_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK1,sK1),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f58,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_relat_2(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f42,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    v2_wellord1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_relat_2(sK0) | ~v2_wellord1(sK0)),
% 0.21/0.50    inference(resolution,[],[f21,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK1,sK1),sK0) | ~v1_relat_2(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f23,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK4(X0),sK4(X0)),X0) & r2_hidden(sK4(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK4(X0),sK4(X0)),X0) & r2_hidden(sK4(X0),k3_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,k3_relat_1(sK0))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1,sK1),sK0) | ~r2_hidden(sK1,k3_relat_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f29,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(k4_tarski(sK1,sK2(X2)),sK0) | ~r2_hidden(k4_tarski(sK1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(k4_tarski(X2,sK2(X2)),sK0) | ~r2_hidden(k4_tarski(sK1,X2),sK0) | ~r2_hidden(X2,k3_relat_1(sK0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (609)------------------------------
% 0.21/0.50  % (609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (609)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (609)Memory used [KB]: 1663
% 0.21/0.50  % (609)Time elapsed: 0.071 s
% 0.21/0.50  % (609)------------------------------
% 0.21/0.50  % (609)------------------------------
% 0.21/0.50  % (604)Success in time 0.135 s
%------------------------------------------------------------------------------

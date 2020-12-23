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
% DateTime   : Thu Dec  3 13:04:06 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   38 (  67 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 ( 380 expanded)
%              Number of equality atoms :  141 ( 174 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f21,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

fof(f38,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f21,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f78,plain,(
    ~ v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X4
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X4
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(f77,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f57,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ r2_hidden(sK0,X0)
      | ~ v1_funct_2(sK2,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK2,X0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f55,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
      | ~ v1_funct_2(sK2,X0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f24,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (24900)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (24909)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.53  % (24904)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (24916)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.53  % (24917)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (24899)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (24899)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f79,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(subsumption_resolution,[],[f78,f42])).
% 1.25/0.54  fof(f42,plain,(
% 1.25/0.54    v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.54    inference(definition_unfolding,[],[f21,f40])).
% 1.25/0.54  fof(f40,plain,(
% 1.25/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.25/0.54    inference(definition_unfolding,[],[f38,f39])).
% 1.25/0.54  fof(f39,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
% 1.25/0.54  fof(f38,plain,(
% 1.25/0.54    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f14,plain,(
% 1.25/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 1.25/0.54  fof(f13,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f9,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.25/0.54    inference(flattening,[],[f8])).
% 1.25/0.54  fof(f8,plain,(
% 1.25/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,negated_conjecture,(
% 1.25/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.25/0.54    inference(negated_conjecture,[],[f6])).
% 1.25/0.54  fof(f6,conjecture,(
% 1.25/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.25/0.54  fof(f78,plain,(
% 1.25/0.54    ~v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.54    inference(subsumption_resolution,[],[f77,f44])).
% 1.25/0.54  fof(f44,plain,(
% 1.25/0.54    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7))) )),
% 1.25/0.54    inference(equality_resolution,[],[f43])).
% 1.25/0.54  fof(f43,plain,(
% 1.25/0.54    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X7) != X5) )),
% 1.25/0.54    inference(equality_resolution,[],[f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.25/0.54    inference(cnf_transformation,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.25/0.54  fof(f18,plain,(
% 1.25/0.54    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f17,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.25/0.54    inference(rectify,[],[f16])).
% 1.25/0.54  fof(f16,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.25/0.54    inference(flattening,[],[f15])).
% 1.25/0.54  fof(f15,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 1.25/0.54    inference(nnf_transformation,[],[f10])).
% 1.25/0.54  fof(f10,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 1.25/0.54    inference(ennf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).
% 1.25/0.54  fof(f77,plain,(
% 1.25/0.54    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~v1_funct_2(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.25/0.54    inference(resolution,[],[f57,f41])).
% 1.25/0.54  fof(f41,plain,(
% 1.25/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))),
% 1.25/0.54    inference(definition_unfolding,[],[f22,f40])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f57,plain,(
% 1.25/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~r2_hidden(sK0,X0) | ~v1_funct_2(sK2,X0,sK1)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f56,f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    v1_funct_1(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    ( ! [X0] : (~r2_hidden(sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK2,X0,sK1) | ~v1_funct_1(sK2)) )),
% 1.25/0.54    inference(subsumption_resolution,[],[f55,f23])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    k1_xboole_0 != sK1),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK2,X0,sK1) | ~v1_funct_1(sK2)) )),
% 1.25/0.54    inference(resolution,[],[f24,f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f12])).
% 1.25/0.54  fof(f12,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.25/0.54    inference(flattening,[],[f11])).
% 1.25/0.54  fof(f11,plain,(
% 1.25/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  % SZS output end Proof for theBenchmark
% 1.25/0.54  % (24899)------------------------------
% 1.25/0.54  % (24899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (24899)Termination reason: Refutation
% 1.25/0.54  
% 1.25/0.54  % (24899)Memory used [KB]: 1791
% 1.25/0.54  % (24899)Time elapsed: 0.115 s
% 1.25/0.54  % (24899)------------------------------
% 1.25/0.54  % (24899)------------------------------
% 1.25/0.54  % (24906)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.54  % (24891)Success in time 0.166 s
%------------------------------------------------------------------------------

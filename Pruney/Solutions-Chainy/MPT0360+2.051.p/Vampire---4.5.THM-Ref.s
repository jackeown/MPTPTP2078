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
% DateTime   : Thu Dec  3 12:44:55 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 227 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f30,f79])).

fof(f79,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f58,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK2)
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f49,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,sK2)
      | ~ r1_tarski(X1,k3_subset_1(sK0,sK2)) ) ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f41,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (16162)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (16178)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (16162)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (16170)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f108,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f107])).
% 1.32/0.54  fof(f107,plain,(
% 1.32/0.54    k1_xboole_0 != k1_xboole_0),
% 1.32/0.54    inference(superposition,[],[f30,f79])).
% 1.32/0.55  fof(f79,plain,(
% 1.32/0.55    k1_xboole_0 = sK1),
% 1.32/0.55    inference(resolution,[],[f78,f31])).
% 1.32/0.55  fof(f31,plain,(
% 1.32/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.55    inference(cnf_transformation,[],[f20])).
% 1.32/0.55  fof(f20,plain,(
% 1.32/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f19])).
% 1.32/0.55  fof(f19,plain,(
% 1.32/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f12,plain,(
% 1.32/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.32/0.55    inference(ennf_transformation,[],[f3])).
% 1.32/0.55  fof(f3,axiom,(
% 1.32/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.32/0.55  fof(f78,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 1.32/0.55    inference(duplicate_literal_removal,[],[f76])).
% 1.32/0.55  fof(f76,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f58,f28])).
% 1.32/0.55  fof(f28,plain,(
% 1.32/0.55    r1_tarski(sK1,sK2)),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f18,plain,(
% 1.32/0.55    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17])).
% 1.32/0.55  fof(f17,plain,(
% 1.32/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f11,plain,(
% 1.32/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(flattening,[],[f10])).
% 1.32/0.55  fof(f10,plain,(
% 1.32/0.55    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f8])).
% 1.32/0.55  fof(f8,negated_conjecture,(
% 1.32/0.55    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.32/0.55    inference(negated_conjecture,[],[f7])).
% 1.32/0.55  fof(f7,conjecture,(
% 1.32/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.32/0.55  fof(f58,plain,(
% 1.32/0.55    ( ! [X4,X3] : (~r1_tarski(X4,sK2) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f52,f37])).
% 1.32/0.55  fof(f37,plain,(
% 1.32/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f26])).
% 1.32/0.55  fof(f26,plain,(
% 1.32/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 1.32/0.55  fof(f25,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f24,plain,(
% 1.32/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.55    inference(rectify,[],[f23])).
% 1.32/0.55  fof(f23,plain,(
% 1.32/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.55    inference(nnf_transformation,[],[f15])).
% 1.32/0.55  fof(f15,plain,(
% 1.32/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f1])).
% 1.32/0.55  fof(f1,axiom,(
% 1.32/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.55  fof(f52,plain,(
% 1.32/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 1.32/0.55    inference(resolution,[],[f50,f29])).
% 1.32/0.55  fof(f29,plain,(
% 1.32/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f50,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k3_subset_1(sK0,sK2)) | ~r2_hidden(X1,sK2) | ~r2_hidden(X1,X0)) )),
% 1.32/0.55    inference(resolution,[],[f49,f35])).
% 1.32/0.55  fof(f35,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.32/0.55    inference(cnf_transformation,[],[f22])).
% 1.32/0.55  fof(f22,plain,(
% 1.32/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f21])).
% 1.32/0.55  fof(f21,plain,(
% 1.32/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.32/0.55    introduced(choice_axiom,[])).
% 1.32/0.55  fof(f13,plain,(
% 1.32/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.32/0.55    inference(ennf_transformation,[],[f9])).
% 1.32/0.55  fof(f9,plain,(
% 1.32/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.55    inference(rectify,[],[f2])).
% 1.32/0.55  fof(f2,axiom,(
% 1.32/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.32/0.55  fof(f49,plain,(
% 1.32/0.55    ( ! [X1] : (r1_xboole_0(X1,sK2) | ~r1_tarski(X1,k3_subset_1(sK0,sK2))) )),
% 1.32/0.55    inference(superposition,[],[f43,f47])).
% 1.32/0.55  fof(f47,plain,(
% 1.32/0.55    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.32/0.55    inference(resolution,[],[f42,f27])).
% 1.32/0.55  fof(f27,plain,(
% 1.32/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  fof(f42,plain,(
% 1.32/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f36,f32])).
% 1.32/0.55  fof(f32,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f4])).
% 1.32/0.55  fof(f4,axiom,(
% 1.32/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.55  fof(f36,plain,(
% 1.32/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f14])).
% 1.32/0.55  fof(f14,plain,(
% 1.32/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.55    inference(ennf_transformation,[],[f6])).
% 1.32/0.55  fof(f6,axiom,(
% 1.32/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.32/0.55  fof(f43,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 1.32/0.55    inference(definition_unfolding,[],[f41,f32])).
% 1.32/0.55  fof(f41,plain,(
% 1.32/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 1.32/0.55    inference(cnf_transformation,[],[f16])).
% 1.32/0.55  fof(f16,plain,(
% 1.32/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.32/0.55    inference(ennf_transformation,[],[f5])).
% 1.32/0.55  fof(f5,axiom,(
% 1.32/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.32/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.32/0.55  fof(f30,plain,(
% 1.32/0.55    k1_xboole_0 != sK1),
% 1.32/0.55    inference(cnf_transformation,[],[f18])).
% 1.32/0.55  % SZS output end Proof for theBenchmark
% 1.32/0.55  % (16162)------------------------------
% 1.32/0.55  % (16162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (16162)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (16162)Memory used [KB]: 6268
% 1.32/0.55  % (16162)Time elapsed: 0.128 s
% 1.32/0.55  % (16162)------------------------------
% 1.32/0.55  % (16162)------------------------------
% 1.32/0.55  % (16149)Success in time 0.188 s
%------------------------------------------------------------------------------

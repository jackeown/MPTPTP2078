%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 174 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  206 ( 898 expanded)
%              Number of equality atoms :   15 (  88 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(subsumption_resolution,[],[f327,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,sK0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),sK0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f327,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f307,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f307,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f261,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f261,plain,(
    ~ r2_hidden(sK4(sK0),sK0) ),
    inference(subsumption_resolution,[],[f252,f202])).

fof(f202,plain,(
    ~ r2_hidden(sK2(sK4(sK0)),sK0) ),
    inference(resolution,[],[f192,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,sK4(X1)) ) ),
    inference(condensation,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f192,plain,(
    r2_hidden(sK2(sK4(sK0)),sK4(sK0)) ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f190,plain,
    ( r2_hidden(sK2(sK4(sK0)),sK4(sK0))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f92,f34])).

fof(f92,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r2_hidden(sK2(sK4(sK0)),sK4(sK0)) ) ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f60,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f60,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(X0),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f27,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | v3_ordinal1(sK2(X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f32,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f252,plain,
    ( ~ r2_hidden(sK4(sK0),sK0)
    | r2_hidden(sK2(sK4(sK0)),sK0) ),
    inference(resolution,[],[f244,f31])).

fof(f31,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | r2_hidden(sK2(X2),sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f244,plain,(
    v3_ordinal1(sK4(sK0)) ),
    inference(subsumption_resolution,[],[f242,f29])).

fof(f242,plain,
    ( v3_ordinal1(sK4(sK0))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f102,f34])).

fof(f102,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v3_ordinal1(sK4(sK0)) ) ),
    inference(resolution,[],[f86,f38])).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v3_ordinal1(X3) ) ),
    inference(subsumption_resolution,[],[f85,f27])).

fof(f85,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v3_ordinal1(X3)
      | ~ v3_ordinal1(sK1) ) ),
    inference(resolution,[],[f69,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:14:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (15596)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (15604)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (15595)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (15595)Refutation not found, incomplete strategy% (15595)------------------------------
% 0.21/0.48  % (15595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15603)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (15596)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (15595)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15595)Memory used [KB]: 10746
% 0.21/0.49  % (15595)Time elapsed: 0.061 s
% 0.21/0.49  % (15595)------------------------------
% 0.21/0.49  % (15595)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f327,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X2] : ((~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f307,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f261,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    ~r2_hidden(sK2(sK4(sK0)),sK0)),
% 0.21/0.49    inference(resolution,[],[f192,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,sK4(X1))) )),
% 0.21/0.49    inference(condensation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    r2_hidden(sK2(sK4(sK0)),sK4(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f190,f29])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    r2_hidden(sK2(sK4(sK0)),sK4(sK0)) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f92,f34])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(sK2(sK4(sK0)),sK4(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f75,f38])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f60,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f46,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_tarski(X1,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f28,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK2(X0),X0) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f58,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (v3_ordinal1(X0) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f27,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v3_ordinal1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(X0,sK0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2] : (~v3_ordinal1(X2) | ~r2_hidden(X2,sK0) | v3_ordinal1(sK2(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f32,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0),sK0) | r2_hidden(sK2(sK4(sK0)),sK0)),
% 0.21/0.49    inference(resolution,[],[f244,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2] : (~v3_ordinal1(X2) | ~r2_hidden(X2,sK0) | r2_hidden(sK2(X2),sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    v3_ordinal1(sK4(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f242,f29])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    v3_ordinal1(sK4(sK0)) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f102,f34])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | v3_ordinal1(sK4(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f86,f38])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK0) | v3_ordinal1(X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f27])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X3] : (~r2_hidden(X3,sK0) | v3_ordinal1(X3) | ~v3_ordinal1(sK1)) )),
% 0.21/0.49    inference(resolution,[],[f69,f35])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15596)------------------------------
% 0.21/0.49  % (15596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15596)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15596)Memory used [KB]: 1791
% 0.21/0.49  % (15596)Time elapsed: 0.073 s
% 0.21/0.49  % (15596)------------------------------
% 0.21/0.49  % (15596)------------------------------
% 0.21/0.50  % (15600)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (15591)Success in time 0.135 s
%------------------------------------------------------------------------------

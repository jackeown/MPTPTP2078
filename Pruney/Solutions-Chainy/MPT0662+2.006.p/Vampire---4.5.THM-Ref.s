%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:12 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   48 (  87 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 349 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

% (23484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f22,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f91,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f86,f29])).

fof(f29,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f84,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2) ),
    inference(subsumption_resolution,[],[f83,f26])).

fof(f83,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f82,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK1),X0)
      | r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),X0) ) ),
    inference(resolution,[],[f78,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f78,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f74,f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f57,f27])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(k4_tarski(X1,k1_funct_1(k7_relat_1(X2,X3),X1)),k7_relat_1(X2,X3))
      | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f55,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
      | r2_hidden(k4_tarski(X1,k1_funct_1(k7_relat_1(X2,X3),X1)),k7_relat_1(X2,X3))
      | ~ v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.46/0.56  % (23475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.56  % (23476)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.57  % (23475)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % (23491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.57  % (23492)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.57  % (23483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f92,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(subsumption_resolution,[],[f91,f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    v1_relat_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  % (23484)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f11,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.46/0.57    inference(flattening,[],[f10])).
% 1.46/0.57  fof(f10,plain,(
% 1.46/0.57    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 1.46/0.57    inference(negated_conjecture,[],[f7])).
% 1.46/0.57  fof(f7,conjecture,(
% 1.46/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).
% 1.46/0.57  fof(f91,plain,(
% 1.46/0.57    ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f90,f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    v1_funct_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f90,plain,(
% 1.46/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f86,f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f86,plain,(
% 1.46/0.57    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(resolution,[],[f84,f40])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(flattening,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(nnf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(flattening,[],[f19])).
% 1.46/0.57  fof(f19,plain,(
% 1.46/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.46/0.57    inference(ennf_transformation,[],[f6])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.46/0.57  fof(f84,plain,(
% 1.46/0.57    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f83,f26])).
% 1.46/0.57  fof(f83,plain,(
% 1.46/0.57    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(resolution,[],[f82,f35])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.46/0.57  fof(f82,plain,(
% 1.46/0.57    ( ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK1),X0) | r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),X0)) )),
% 1.46/0.57    inference(resolution,[],[f78,f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f18])).
% 1.46/0.57  fof(f18,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.58  fof(f78,plain,(
% 1.46/0.58    r2_hidden(k4_tarski(sK0,k1_funct_1(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))),
% 1.46/0.58    inference(resolution,[],[f76,f28])).
% 1.46/0.58  fof(f28,plain,(
% 1.46/0.58    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 1.46/0.58    inference(cnf_transformation,[],[f22])).
% 1.46/0.58  fof(f76,plain,(
% 1.46/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1))) )),
% 1.46/0.58    inference(subsumption_resolution,[],[f74,f26])).
% 1.46/0.58  fof(f74,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,k1_funct_1(k7_relat_1(sK2,X1),X0)),k7_relat_1(sK2,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 1.46/0.58    inference(resolution,[],[f57,f27])).
% 1.46/0.58  fof(f57,plain,(
% 1.46/0.58    ( ! [X2,X3,X1] : (~v1_funct_1(X2) | r2_hidden(k4_tarski(X1,k1_funct_1(k7_relat_1(X2,X3),X1)),k7_relat_1(X2,X3)) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3))) | ~v1_relat_1(X2)) )),
% 1.46/0.58    inference(subsumption_resolution,[],[f55,f34])).
% 1.46/0.58  fof(f34,plain,(
% 1.46/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f14])).
% 1.46/0.58  fof(f14,plain,(
% 1.46/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(ennf_transformation,[],[f2])).
% 1.46/0.58  fof(f2,axiom,(
% 1.46/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.46/0.58  fof(f55,plain,(
% 1.46/0.58    ( ! [X2,X3,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3))) | r2_hidden(k4_tarski(X1,k1_funct_1(k7_relat_1(X2,X3),X1)),k7_relat_1(X2,X3)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.46/0.58    inference(resolution,[],[f44,f37])).
% 1.46/0.58  fof(f37,plain,(
% 1.46/0.58    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f17])).
% 1.46/0.58  fof(f17,plain,(
% 1.46/0.58    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(flattening,[],[f16])).
% 1.46/0.58  fof(f16,plain,(
% 1.46/0.58    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.58    inference(ennf_transformation,[],[f5])).
% 1.46/0.58  fof(f5,axiom,(
% 1.46/0.58    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.46/0.58  fof(f44,plain,(
% 1.46/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(equality_resolution,[],[f30])).
% 1.46/0.58  fof(f30,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f23])).
% 1.46/0.58  fof(f23,plain,(
% 1.46/0.58    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(nnf_transformation,[],[f13])).
% 1.46/0.58  fof(f13,plain,(
% 1.46/0.58    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.58    inference(flattening,[],[f12])).
% 1.46/0.58  fof(f12,plain,(
% 1.46/0.58    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.58    inference(ennf_transformation,[],[f4])).
% 1.46/0.58  fof(f4,axiom,(
% 1.46/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 1.46/0.58  % SZS output end Proof for theBenchmark
% 1.46/0.58  % (23475)------------------------------
% 1.46/0.58  % (23475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (23475)Termination reason: Refutation
% 1.46/0.58  
% 1.46/0.58  % (23475)Memory used [KB]: 6268
% 1.46/0.58  % (23475)Time elapsed: 0.121 s
% 1.46/0.58  % (23475)------------------------------
% 1.46/0.58  % (23475)------------------------------
% 1.46/0.58  % (23467)Success in time 0.214 s
%------------------------------------------------------------------------------

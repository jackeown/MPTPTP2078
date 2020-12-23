%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 191 expanded)
%              Number of leaves         :    5 (  37 expanded)
%              Depth                    :   20
%              Number of atoms          :  167 ( 675 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1316,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f1316,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1315,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f1315,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f1311,f14])).

fof(f14,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f1311,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f1303,f22])).

fof(f1303,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f1299,f1086])).

fof(f1086,plain,
    ( ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f302,f946])).

fof(f946,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) ),
    inference(resolution,[],[f943,f63])).

fof(f63,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | r2_hidden(k4_tarski(X1,X2),sK3) ) ),
    inference(subsumption_resolution,[],[f62,f18])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | r2_hidden(k4_tarski(X1,X2),sK3) ) ),
    inference(resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f943,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) ),
    inference(subsumption_resolution,[],[f939,f18])).

fof(f939,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f415,f22])).

fof(f415,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) ),
    inference(subsumption_resolution,[],[f404,f18])).

fof(f404,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) ),
    inference(resolution,[],[f200,f31])).

fof(f31,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f200,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f196,f18])).

fof(f196,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f22])).

fof(f66,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f302,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)
    | ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f292,f14])).

fof(f292,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k8_relat_1(sK1,sK3))
    | ~ r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) ),
    inference(resolution,[],[f67,f30])).

fof(f30,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1299,plain,(
    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f1295,f18])).

fof(f1295,plain,
    ( r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1294,f22])).

fof(f1294,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f1280,f18])).

fof(f1280,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) ),
    inference(resolution,[],[f1278,f32])).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1278,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1274,f18])).

fof(f1274,plain,
    ( r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f481,f22])).

fof(f481,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f180,f200])).

fof(f180,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK0,sK2))
      | ~ v1_relat_1(k8_relat_1(sK1,sK2))
      | r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f176,f168])).

fof(f168,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f22,f113])).

fof(f113,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f64,f18])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0) ) ),
    inference(resolution,[],[f16,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f176,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK0,sK2))
      | ~ v1_relat_1(k8_relat_1(sK1,sK2))
      | ~ v1_relat_1(k8_relat_1(sK0,sK2))
      | r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK1,sK2)) ) ),
    inference(superposition,[],[f31,f113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (31045)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (31041)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (31037)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (31049)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31042)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (31038)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31046)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (31038)Refutation not found, incomplete strategy% (31038)------------------------------
% 0.21/0.48  % (31038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31038)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31038)Memory used [KB]: 10490
% 0.21/0.48  % (31038)Time elapsed: 0.073 s
% 0.21/0.48  % (31038)------------------------------
% 0.21/0.48  % (31038)------------------------------
% 0.21/0.49  % (31040)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (31057)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (31057)Refutation not found, incomplete strategy% (31057)------------------------------
% 0.21/0.49  % (31057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31057)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31057)Memory used [KB]: 10490
% 0.21/0.49  % (31057)Time elapsed: 0.070 s
% 0.21/0.49  % (31057)------------------------------
% 0.21/0.49  % (31057)------------------------------
% 0.21/0.50  % (31055)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (31039)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (31053)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (31050)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (31047)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (31056)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (31051)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (31052)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (31048)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (31044)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (31054)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (31043)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.57  % (31050)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1320,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f1316,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f5])).
% 0.21/0.57  fof(f5,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 0.21/0.57  fof(f1316,plain,(
% 0.21/0.57    ~v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f1315,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.57  fof(f1315,plain,(
% 0.21/0.57    ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f1311,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    v1_relat_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f1311,plain,(
% 0.21/0.57    ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK3)),
% 0.21/0.57    inference(resolution,[],[f1303,f22])).
% 0.21/0.57  fof(f1303,plain,(
% 0.21/0.57    ~v1_relat_1(k8_relat_1(sK1,sK3)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.57    inference(resolution,[],[f1299,f1086])).
% 0.21/0.57  fof(f1086,plain,(
% 0.21/0.57    ~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~v1_relat_1(k8_relat_1(sK1,sK3)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.57    inference(resolution,[],[f302,f946])).
% 0.21/0.57  fof(f946,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)),
% 0.21/0.57    inference(resolution,[],[f943,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | r2_hidden(k4_tarski(X1,X2),sK3)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f62,f18])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X1,X2),sK2) | r2_hidden(k4_tarski(X1,X2),sK3)) )),
% 0.21/0.57    inference(resolution,[],[f15,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    r1_tarski(sK2,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f943,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f939,f18])).
% 0.21/0.57  fof(f939,plain,(
% 0.21/0.57    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2) | ~v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f415,f22])).
% 0.21/0.57  fof(f415,plain,(
% 0.21/0.57    ~v1_relat_1(k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f404,f18])).
% 0.21/0.57  fof(f404,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK2)),
% 0.21/0.57    inference(resolution,[],[f200,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 1.82/0.58  fof(f200,plain,(
% 1.82/0.58    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2))),
% 1.82/0.58    inference(subsumption_resolution,[],[f196,f18])).
% 1.82/0.58  fof(f196,plain,(
% 1.82/0.58    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2)),
% 1.82/0.58    inference(resolution,[],[f66,f22])).
% 1.82/0.58  fof(f66,plain,(
% 1.82/0.58    ~v1_relat_1(k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2))),
% 1.82/0.58    inference(resolution,[],[f17,f20])).
% 1.82/0.58  fof(f20,plain,(
% 1.82/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.82/0.58    inference(cnf_transformation,[],[f9])).
% 1.82/0.58  fof(f17,plain,(
% 1.82/0.58    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.82/0.58    inference(cnf_transformation,[],[f8])).
% 1.82/0.58  fof(f302,plain,(
% 1.82/0.58    ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3) | ~v1_relat_1(k8_relat_1(sK1,sK3)) | ~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.82/0.58    inference(subsumption_resolution,[],[f292,f14])).
% 1.82/0.58  fof(f292,plain,(
% 1.82/0.58    ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK3) | ~v1_relat_1(k8_relat_1(sK1,sK3)) | ~r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),sK3)),
% 1.82/0.58    inference(resolution,[],[f67,f30])).
% 1.82/0.58  fof(f30,plain,(
% 1.82/0.58    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 1.82/0.58    inference(equality_resolution,[],[f28])).
% 1.82/0.58  fof(f28,plain,(
% 1.82/0.58    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 1.82/0.58    inference(cnf_transformation,[],[f11])).
% 1.82/0.58  fof(f67,plain,(
% 1.82/0.58    ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.82/0.58    inference(resolution,[],[f17,f21])).
% 1.82/0.58  fof(f21,plain,(
% 1.82/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 1.82/0.58    inference(cnf_transformation,[],[f9])).
% 1.82/0.58  fof(f1299,plain,(
% 1.82/0.58    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)),
% 1.82/0.58    inference(subsumption_resolution,[],[f1295,f18])).
% 1.82/0.58  fof(f1295,plain,(
% 1.82/0.58    r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1) | ~v1_relat_1(sK2)),
% 1.82/0.58    inference(resolution,[],[f1294,f22])).
% 1.82/0.58  fof(f1294,plain,(
% 1.82/0.58    ~v1_relat_1(k8_relat_1(sK1,sK2)) | r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)),
% 1.82/0.58    inference(subsumption_resolution,[],[f1280,f18])).
% 1.82/0.58  fof(f1280,plain,(
% 1.82/0.58    ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | r2_hidden(sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK1)),
% 1.82/0.58    inference(resolution,[],[f1278,f32])).
% 1.82/0.58  fof(f32,plain,(
% 1.82/0.58    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 1.82/0.58    inference(equality_resolution,[],[f26])).
% 1.82/0.58  fof(f26,plain,(
% 1.82/0.58    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 1.82/0.58    inference(cnf_transformation,[],[f11])).
% 1.82/0.58  fof(f1278,plain,(
% 1.82/0.58    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))),
% 1.82/0.58    inference(subsumption_resolution,[],[f1274,f18])).
% 1.82/0.58  fof(f1274,plain,(
% 1.82/0.58    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2)),
% 1.82/0.58    inference(resolution,[],[f481,f22])).
% 1.82/0.58  fof(f481,plain,(
% 1.82/0.58    ~v1_relat_1(k8_relat_1(sK1,sK2)) | r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))),
% 1.82/0.58    inference(resolution,[],[f180,f200])).
% 1.82/0.58  fof(f180,plain,(
% 1.82/0.58    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK1,sK2))) )),
% 1.82/0.58    inference(subsumption_resolution,[],[f176,f168])).
% 1.82/0.58  fof(f168,plain,(
% 1.82/0.58    ~v1_relat_1(k8_relat_1(sK1,sK2)) | v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.82/0.58    inference(superposition,[],[f22,f113])).
% 1.82/0.58  fof(f113,plain,(
% 1.82/0.58    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 1.82/0.58    inference(resolution,[],[f64,f18])).
% 1.82/0.58  fof(f64,plain,(
% 1.82/0.58    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(sK0,k8_relat_1(sK1,X0)) = k8_relat_1(sK0,X0)) )),
% 1.82/0.58    inference(resolution,[],[f16,f29])).
% 1.82/0.58  fof(f29,plain,(
% 1.82/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)) )),
% 1.82/0.58    inference(cnf_transformation,[],[f13])).
% 1.82/0.58  fof(f13,plain,(
% 1.82/0.58    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.82/0.58    inference(flattening,[],[f12])).
% 1.82/0.58  fof(f12,plain,(
% 1.82/0.58    ! [X0,X1,X2] : ((k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.82/0.58    inference(ennf_transformation,[],[f4])).
% 1.82/0.58  fof(f4,axiom,(
% 1.82/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(X0,X2)))),
% 1.82/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).
% 1.82/0.58  fof(f16,plain,(
% 1.82/0.58    r1_tarski(sK0,sK1)),
% 1.82/0.58    inference(cnf_transformation,[],[f8])).
% 1.82/0.58  fof(f176,plain,(
% 1.82/0.58    ( ! [X10,X9] : (~r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X9,X10),k8_relat_1(sK1,sK2))) )),
% 1.82/0.58    inference(superposition,[],[f31,f113])).
% 1.82/0.58  % SZS output end Proof for theBenchmark
% 1.82/0.58  % (31050)------------------------------
% 1.82/0.58  % (31050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.58  % (31050)Termination reason: Refutation
% 1.82/0.58  
% 1.82/0.58  % (31050)Memory used [KB]: 2430
% 1.82/0.58  % (31050)Time elapsed: 0.151 s
% 1.82/0.58  % (31050)------------------------------
% 1.82/0.58  % (31050)------------------------------
% 1.82/0.58  % (31036)Success in time 0.23 s
%------------------------------------------------------------------------------

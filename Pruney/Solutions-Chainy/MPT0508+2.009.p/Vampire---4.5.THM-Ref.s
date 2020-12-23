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
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 150 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   18
%              Number of atoms          :  157 ( 533 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1284,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f1284,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1283,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1283,plain,(
    ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1279,f17])).

fof(f17,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f1279,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f1278,f31])).

fof(f1278,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1262,f496])).

fof(f496,plain,(
    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f492,f21])).

fof(f492,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f466,f31])).

fof(f466,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) ),
    inference(resolution,[],[f266,f185])).

fof(f185,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(k4_tarski(X14,X15),k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | r2_hidden(X14,sK1) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(k4_tarski(X14,X15),k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | ~ v1_relat_1(k7_relat_1(sK2,sK0))
      | r2_hidden(X14,sK1) ) ),
    inference(superposition,[],[f36,f143])).

fof(f143,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f73,f21])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1) ) ),
    inference(resolution,[],[f19,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f266,plain,(
    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f262,f21])).

fof(f262,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f31])).

fof(f76,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f20,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1262,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f1248,f397])).

fof(f397,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f387,f17])).

fof(f387,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) ),
    inference(resolution,[],[f77,f34])).

fof(f34,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f20,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1248,plain,(
    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) ),
    inference(resolution,[],[f1243,f72])).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | r2_hidden(k4_tarski(X2,X3),sK3) ) ),
    inference(subsumption_resolution,[],[f71,f21])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | r2_hidden(k4_tarski(X2,X3),sK3) ) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f1243,plain,(
    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f1239,f21])).

fof(f1239,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f479,f31])).

fof(f479,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) ),
    inference(subsumption_resolution,[],[f468,f21])).

fof(f468,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) ),
    inference(resolution,[],[f266,f35])).

fof(f35,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (23436)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (23429)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (23428)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (23436)Refutation not found, incomplete strategy% (23436)------------------------------
% 0.20/0.48  % (23436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23436)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23436)Memory used [KB]: 10490
% 0.20/0.48  % (23436)Time elapsed: 0.061 s
% 0.20/0.48  % (23436)------------------------------
% 0.20/0.48  % (23436)------------------------------
% 0.20/0.49  % (23430)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (23429)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1288,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f1284,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f8])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.50  fof(f1284,plain,(
% 0.20/0.50    ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f1283,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.50  fof(f1283,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f1279,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v1_relat_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f1279,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK3)),
% 0.20/0.50    inference(resolution,[],[f1278,f31])).
% 0.20/0.50  fof(f1278,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f1262,f496])).
% 0.20/0.50  fof(f496,plain,(
% 0.20/0.50    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f492,f21])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f466,f31])).
% 0.20/0.50  fof(f466,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)),
% 0.20/0.50    inference(resolution,[],[f266,f185])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X14,X15] : (~r2_hidden(k4_tarski(X14,X15),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(X14,sK1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X14,X15] : (~r2_hidden(k4_tarski(X14,X15),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(X14,sK1)) )),
% 0.20/0.50    inference(superposition,[],[f36,f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.50    inference(resolution,[],[f73,f21])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1)) )),
% 0.20/0.50    inference(resolution,[],[f19,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    r1_tarski(sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f262,f21])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f76,f31])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(resolution,[],[f20,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f1262,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(resolution,[],[f1248,f397])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) | ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f387,f17])).
% 0.20/0.50  fof(f387,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK3) | ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)),
% 0.20/0.50    inference(resolution,[],[f77,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X0) | r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.50    inference(resolution,[],[f20,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f1248,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)),
% 0.20/0.50    inference(resolution,[],[f1243,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(k4_tarski(X2,X3),sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f21])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(k4_tarski(X2,X3),sK3)) )),
% 0.20/0.50    inference(resolution,[],[f18,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f1243,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f1239,f21])).
% 0.20/0.50  fof(f1239,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f479,f31])).
% 0.20/0.50  fof(f479,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f468,f21])).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)),
% 0.20/0.50    inference(resolution,[],[f266,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (23429)------------------------------
% 0.20/0.50  % (23429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23429)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (23429)Memory used [KB]: 2430
% 0.20/0.50  % (23429)Time elapsed: 0.035 s
% 0.20/0.50  % (23429)------------------------------
% 0.20/0.50  % (23429)------------------------------
% 0.20/0.50  % (23415)Success in time 0.139 s
%------------------------------------------------------------------------------

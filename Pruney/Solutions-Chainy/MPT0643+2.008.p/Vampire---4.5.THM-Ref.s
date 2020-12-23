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
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 207 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   24
%              Number of atoms          :  236 (1439 expanded)
%              Number of equality atoms :   87 ( 566 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f114,f112])).

fof(f112,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f111,f21])).

fof(f21,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f111,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK2 = k6_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK0,sK0)
    | sK0 != sK0
    | sK2 = k6_relat_1(sK0) ),
    inference(superposition,[],[f109,f83])).

fof(f83,plain,(
    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f43,f16])).

fof(f16,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f22,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | ~ r1_tarski(X0,sK0)
      | sK0 != X0
      | k6_relat_1(X0) = sK2 ) ),
    inference(forward_demodulation,[],[f108,f26])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k6_relat_1(X0)) != sK0
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = sK2 ) ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f25,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k6_relat_1(X0)) != sK0
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | k6_relat_1(X0) = sK2 ) ),
    inference(subsumption_resolution,[],[f106,f24])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_relat_1(k6_relat_1(X0)) != sK0
      | sK1 != k5_relat_1(k6_relat_1(X0),sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k6_relat_1(X0) = sK2 ) ),
    inference(superposition,[],[f54,f27])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | k1_relat_1(X0) != sK0
      | sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sK2 = X0 ) ),
    inference(forward_demodulation,[],[f53,f17])).

fof(f17,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0 ) ),
    inference(subsumption_resolution,[],[f52,f18])).

fof(f18,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0 ) ),
    inference(forward_demodulation,[],[f51,f16])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0 ) ),
    inference(forward_demodulation,[],[f50,f16])).

fof(f50,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0 ) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f19,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | sK2 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f48,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | sK2 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f47,f15])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | sK2 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f46,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | sK2 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0] :
      ( sK1 != k5_relat_1(X0,sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK1))
      | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
      | k1_relat_1(X0) != k1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | sK2 = X0
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f36,f20])).

fof(f20,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f114,plain,(
    r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f113,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f113,plain,(
    r2_hidden(sK5(sK0,sK0),sK0) ),
    inference(resolution,[],[f112,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (10405)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.48  % (10405)Refutation not found, incomplete strategy% (10405)------------------------------
% 0.21/0.48  % (10405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10405)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10405)Memory used [KB]: 10746
% 0.21/0.48  % (10405)Time elapsed: 0.067 s
% 0.21/0.48  % (10405)------------------------------
% 0.21/0.48  % (10405)------------------------------
% 0.21/0.49  % (10418)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (10418)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK2 != k6_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | sK2 = k6_relat_1(sK0)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    sK1 != sK1 | ~r1_tarski(sK0,sK0) | sK0 != sK0 | sK2 = k6_relat_1(sK0)),
% 0.21/0.49    inference(superposition,[],[f109,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    sK1 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f43,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.21/0.49    inference(resolution,[],[f22,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(k6_relat_1(X0),sK1) | ~r1_tarski(X0,sK0) | sK0 != X0 | k6_relat_1(X0) = sK2) )),
% 0.21/0.49    inference(forward_demodulation,[],[f108,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k6_relat_1(X0)) != sK0 | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = sK2) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k6_relat_1(X0)) != sK0 | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | ~v1_funct_1(k6_relat_1(X0)) | k6_relat_1(X0) = sK2) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k6_relat_1(X0)) != sK0 | sK1 != k5_relat_1(k6_relat_1(X0),sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k6_relat_1(X0) = sK2) )),
% 0.21/0.49    inference(superposition,[],[f54,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),sK0) | k1_relat_1(X0) != sK0 | sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | sK2 = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f53,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),sK0) | ~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f51,f16])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),sK0) | sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f50,f16])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v2_funct_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f48,f22])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f46,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f44,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (sK1 != k5_relat_1(X0,sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK1)) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | sK2 = X0 | ~v2_funct_1(sK1)) )),
% 0.21/0.49    inference(superposition,[],[f36,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_relat_1(X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    r1_tarski(sK0,sK0)),
% 0.21/0.49    inference(resolution,[],[f113,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0,sK0),sK0)),
% 0.21/0.49    inference(resolution,[],[f112,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10418)------------------------------
% 0.21/0.49  % (10418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10418)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10418)Memory used [KB]: 1791
% 0.21/0.49  % (10418)Time elapsed: 0.085 s
% 0.21/0.49  % (10418)------------------------------
% 0.21/0.49  % (10418)------------------------------
% 0.21/0.50  % (10396)Success in time 0.135 s
%------------------------------------------------------------------------------

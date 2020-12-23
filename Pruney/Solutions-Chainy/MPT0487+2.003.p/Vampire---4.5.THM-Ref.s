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
% DateTime   : Thu Dec  3 12:48:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 221 expanded)
%              Number of leaves         :   11 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  173 (1478 expanded)
%              Number of equality atoms :   65 ( 668 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(subsumption_resolution,[],[f203,f32])).

fof(f32,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK3
    & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X1 != X3
                & k6_relat_1(X0) = k5_relat_1(X2,X3)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                & r1_tarski(k2_relat_1(X1),X0)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != X3
              & k5_relat_1(X2,X3) = k6_relat_1(sK0)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
              & r1_tarski(k2_relat_1(sK1),sK0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != X3
            & k5_relat_1(X2,X3) = k6_relat_1(sK0)
            & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
            & r1_tarski(k2_relat_1(sK1),sK0)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK1 != X3
          & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
          & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
          & r1_tarski(k2_relat_1(sK1),sK0)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( sK1 != X3
        & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
        & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
        & r1_tarski(k2_relat_1(sK1),sK0)
        & v1_relat_1(X3) )
   => ( sK1 != sK3
      & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
      & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).

fof(f203,plain,(
    sK1 = sK3 ),
    inference(backward_demodulation,[],[f129,f196])).

fof(f196,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK3) ),
    inference(backward_demodulation,[],[f126,f181])).

fof(f181,plain,(
    k1_relat_1(sK3) = k1_relat_1(sK1) ),
    inference(superposition,[],[f139,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f139,plain,(
    k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k1_relat_1(sK3))) ),
    inference(forward_demodulation,[],[f135,f30])).

fof(f30,plain,(
    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f135,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f127,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f127,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f123,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f123,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f122,f33])).

fof(f122,plain,(
    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f80,f31])).

fof(f31,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f28,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    inference(backward_demodulation,[],[f116,f124])).

fof(f124,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f29,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f116,plain,(
    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    inference(forward_demodulation,[],[f115,f30])).

fof(f115,plain,(
    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f103,f31])).

fof(f103,plain,(
    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k5_relat_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f129,plain,(
    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK3) ),
    inference(unit_resulting_resolution,[],[f28,f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f75,plain,(
    r1_tarski(k1_relat_1(sK3),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f74,f33])).

fof(f74,plain,(
    r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK3))),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f51,f30])).

fof(f51,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27640)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (27635)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (27632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (27640)Refutation not found, incomplete strategy% (27640)------------------------------
% 0.22/0.48  % (27640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27640)Memory used [KB]: 10618
% 0.22/0.48  % (27640)Time elapsed: 0.061 s
% 0.22/0.48  % (27640)------------------------------
% 0.22/0.48  % (27640)------------------------------
% 0.22/0.48  % (27627)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (27632)Refutation not found, incomplete strategy% (27632)------------------------------
% 0.22/0.48  % (27632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27632)Memory used [KB]: 6012
% 0.22/0.48  % (27632)Time elapsed: 0.004 s
% 0.22/0.48  % (27632)------------------------------
% 0.22/0.48  % (27632)------------------------------
% 0.22/0.49  % (27621)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (27624)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (27635)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f203,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    sK1 != sK3),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ((sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) => (sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (? [X3] : ((X1 != X3 & (k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    sK1 = sK3),
% 0.22/0.49    inference(backward_demodulation,[],[f129,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f126,f181])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relat_1(sK1)),
% 0.22/0.49    inference(superposition,[],[f139,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    k1_relat_1(sK1) = k1_relat_1(k6_relat_1(k1_relat_1(sK3)))),
% 0.22/0.49    inference(forward_demodulation,[],[f135,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK2))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f26,f27,f127,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK2))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f123,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    r1_tarski(sK0,k1_relat_1(sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f122,f33])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f80,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),k1_relat_1(sK2))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f27,f28,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f116,f124])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f26,f29,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 0.22/0.49    inference(forward_demodulation,[],[f115,f30])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f103,f31])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    k5_relat_1(k5_relat_1(sK1,sK2),sK3) = k5_relat_1(sK1,k5_relat_1(sK2,sK3))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f26,f27,f28,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f28,f75,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(sK3),k1_relat_1(sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f74,f33])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(sK3))),k1_relat_1(sK1))),
% 0.22/0.49    inference(forward_demodulation,[],[f51,f30])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relat_1(sK1,sK2)),k1_relat_1(sK1))),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f26,f27,f35])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27635)------------------------------
% 0.22/0.49  % (27635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27635)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27635)Memory used [KB]: 6268
% 0.22/0.49  % (27635)Time elapsed: 0.014 s
% 0.22/0.49  % (27635)------------------------------
% 0.22/0.49  % (27635)------------------------------
% 0.22/0.49  % (27626)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (27619)Success in time 0.132 s
%------------------------------------------------------------------------------

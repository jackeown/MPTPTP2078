%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0600+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 135 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 356 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18982)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f64,plain,(
    $false ),
    inference(global_subsumption,[],[f10,f41,f62])).

fof(f62,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f57,f61])).

fof(f61,plain,(
    sK0 = sK5(sK2,k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f53,plain,(
    r2_hidden(sK5(sK2,k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(sK2,X2))
      | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2)) ) ),
    inference(subsumption_resolution,[],[f35,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f35,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(sK2,X2))
      | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,(
    ! [X4] : k11_relat_1(sK2,X4) = k9_relat_1(sK2,k1_tarski(X4)) ),
    inference(resolution,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

% (18976)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f57,plain,(
    r2_hidden(k4_tarski(sK5(sK2,k1_tarski(sK0),sK1),sK1),sK2) ),
    inference(resolution,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2) ) ),
    inference(subsumption_resolution,[],[f34,f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f28,f31])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f39,f31])).

fof(f39,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0))) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f32,f11])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f9,f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------

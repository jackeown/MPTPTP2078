%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0517+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   25 (  45 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 105 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f10])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k8_relat_1(X0,X1),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f65,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f64,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f64,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f63,f39])).

fof(f39,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f11,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f11,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f55,f10])).

fof(f55,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),sK1) ),
    inference(resolution,[],[f53,f23])).

fof(f23,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f53,plain,(
    r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f49,f10])).

% (30479)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f49,plain,
    ( r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f15])).

fof(f38,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK2(k8_relat_1(sK0,sK1),sK1),sK3(k8_relat_1(sK0,sK1),sK1)),k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f11,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------

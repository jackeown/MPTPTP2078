%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0521+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   23 (  37 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  95 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(resolution,[],[f62,f12])).

fof(f12,plain,(
    ~ r1_tarski(k5_relat_1(k8_relat_1(sK0,sK1),sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k8_relat_1(X0,X1),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_relat_1)).

fof(f62,plain,(
    ! [X1] : r1_tarski(k5_relat_1(k8_relat_1(X1,sK1),sK2),k5_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f61,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k5_relat_1(k8_relat_1(X1,sK1),sK2),k5_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f54,f18])).

fof(f18,plain,(
    ! [X1] : v1_relat_1(k8_relat_1(X1,sK1)) ),
    inference(resolution,[],[f15,f13])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f54,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k8_relat_1(X1,sK1))
      | ~ v1_relat_1(sK1)
      | r1_tarski(k5_relat_1(k8_relat_1(X1,sK1),sK2),k5_relat_1(sK1,sK2)) ) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(k8_relat_1(X1,sK1),sK1) ),
    inference(resolution,[],[f16,f13])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X1,sK2),k5_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f14,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

%------------------------------------------------------------------------------

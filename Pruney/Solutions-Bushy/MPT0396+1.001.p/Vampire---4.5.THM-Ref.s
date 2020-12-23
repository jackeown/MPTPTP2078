%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0396+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:54 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   36 (  61 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 165 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f11])).

fof(f11,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f86,plain,(
    r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    | r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(resolution,[],[f82,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k3_tarski(sK0),X0),k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f77,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(sK0),X0)
      | r2_hidden(sK2(k3_tarski(sK0),X0),k3_tarski(sK1))
      | ~ r2_hidden(sK2(k3_tarski(sK0),X0),k3_tarski(sK0)) ) ),
    inference(resolution,[],[f76,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK5(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK5(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(sK0,sK2(k3_tarski(sK0),X1)))
      | r1_tarski(k3_tarski(sK0),X1)
      | r2_hidden(X0,k3_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f71,f13])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X1)
      | ~ r2_hidden(X0,sK5(sK0,sK2(k3_tarski(sK0),X1)))
      | ~ r2_hidden(sK2(k3_tarski(sK0),X1),k3_tarski(sK0)) ) ),
    inference(resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,sK3(sK1,sK5(sK0,X3)))
      | ~ r2_hidden(X2,sK5(sK0,X3))
      | ~ r2_hidden(X3,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X1,sK3(sK1,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f38,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK3(sK1,X0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f16,f10])).

fof(f10,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3(sK1,sK5(sK0,sK2(k3_tarski(sK0),X1))))
      | r2_hidden(X0,k3_tarski(sK1))
      | r1_tarski(k3_tarski(sK0),X1) ) ),
    inference(resolution,[],[f35,f13])).

fof(f35,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k3_tarski(sK0))
      | r2_hidden(X2,k3_tarski(sK1))
      | ~ r2_hidden(X2,sK3(sK1,sK5(sK0,X3))) ) ),
    inference(resolution,[],[f33,f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK3(sK1,X0))
      | r2_hidden(X1,k3_tarski(sK1)) ) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f15,f10])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK3(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------

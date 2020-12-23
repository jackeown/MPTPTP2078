%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t218_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  59 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 227 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v5_relat_1(sK2,sK1)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v5_relat_1(X2,X1)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v5_relat_1(X2,sK1)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( ~ v5_relat_1(sK2,X1)
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v5_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t218_relat_1.p',t218_relat_1)).

fof(f42,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f38,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t218_relat_1.p',d19_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( v5_relat_1(sK2,X0)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t218_relat_1.p',t1_xboole_1)).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 551 expanded)
%              Number of leaves         :    7 ( 128 expanded)
%              Depth                    :   28
%              Number of atoms          :  299 (2430 expanded)
%              Number of equality atoms :   45 ( 420 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(subsumption_resolution,[],[f297,f16])).

fof(f16,plain,(
    ~ r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_wellord1)).

fof(f297,plain,(
    r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f296,f15])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f296,plain,
    ( ~ v1_relat_1(sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f295,f124])).

fof(f124,plain,(
    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f122,f72])).

fof(f72,plain,(
    sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f65,f15])).

fof(f65,plain,
    ( ~ v1_relat_1(sK0)
    | sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f63,f16])).

fof(f63,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | sK2(X0,X0,k6_relat_1(k3_relat_1(X0))) = k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))) ) ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f61,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2,X2,k6_relat_1(k3_relat_1(X2))),k3_relat_1(X2))
      | r3_wellord1(X2,X2,k6_relat_1(k3_relat_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f58,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f58,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X2,X2,k6_relat_1(k3_relat_1(X2))),sK2(X2,X2,k6_relat_1(k3_relat_1(X2)))),X2)
      | r3_wellord1(X2,X2,k6_relat_1(k3_relat_1(X2)))
      | r2_hidden(sK2(X2,X2,k6_relat_1(k3_relat_1(X2))),k3_relat_1(X2)) ) ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X3,X2,X1,X0)
      | r2_hidden(X4,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).

fof(f55,plain,(
    ! [X0] :
      ( sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0)
      | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0)
      | r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0)
      | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X0) != k3_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | sP3(sK2(X1,X0,k6_relat_1(k3_relat_1(X1))),sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),k6_relat_1(k3_relat_1(X1)),X0,X1)
      | r2_hidden(k4_tarski(sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),sK2(X1,X0,k6_relat_1(k3_relat_1(X1)))),X1)
      | r3_wellord1(X1,X0,k6_relat_1(k3_relat_1(X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X2) != X0
      | k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f45,f21])).

fof(f21,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f44,f18])).

fof(f18,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f43,f20])).

fof(f20,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f42,f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(superposition,[],[f27,f22])).

fof(f22,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X2)
      | sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X2,X1,X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f121,f15])).

fof(f121,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f116,f16])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f57,f82])).

fof(f82,plain,(
    sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f75,f15])).

fof(f75,plain,
    ( ~ v1_relat_1(sK0)
    | sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f64,f16])).

fof(f64,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | sK1(X0,X0,k6_relat_1(k3_relat_1(X0))) = k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK1(X0,X0,k6_relat_1(k3_relat_1(X0)))) ) ),
    inference(resolution,[],[f62,f34])).

fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),k3_relat_1(X3))
      | r3_wellord1(X3,X3,k6_relat_1(k3_relat_1(X3)))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),sK2(X3,X3,k6_relat_1(k3_relat_1(X3)))),X3)
      | r3_wellord1(X3,X3,k6_relat_1(k3_relat_1(X3)))
      | r2_hidden(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),k3_relat_1(X3)) ) ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X3,X2,X1,X0)
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK1(X1,X1,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK2(X1,X1,k6_relat_1(k3_relat_1(X1))))),X1)
      | r2_hidden(k4_tarski(sK1(X1,X1,k6_relat_1(k3_relat_1(X1))),sK2(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1)
      | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f55,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X3,X2,X1,X0)
      | r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f295,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f294,f131])).

fof(f131,plain,(
    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f127,f15])).

fof(f127,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f124,f35])).

fof(f294,plain,
    ( ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f293,f130])).

fof(f130,plain,(
    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f126,f15])).

fof(f126,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f124,f36])).

fof(f293,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(resolution,[],[f86,f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0)
      | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0)
      | ~ r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0)
      | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X0) != k3_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ sP3(sK2(X1,X0,k6_relat_1(k3_relat_1(X1))),sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),k6_relat_1(k3_relat_1(X1)),X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),sK2(X1,X0,k6_relat_1(k3_relat_1(X1)))),X1)
      | r3_wellord1(X1,X0,k6_relat_1(k3_relat_1(X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X2) != X0
      | k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f51,f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f49,f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f48,f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(k6_relat_1(X0))
      | ~ sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2)
      | ~ r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2)
      | r3_wellord1(X2,X1,k6_relat_1(X0)) ) ),
    inference(superposition,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X2)
      | ~ sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X2,X1,X0)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X2,X3] :
      ( sP3(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k6_relat_1(k3_relat_1(sK0)),X2,X3)
      | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X3))
      | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X3))
      | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),X2) ) ),
    inference(superposition,[],[f73,f82])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),X0),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),X1)
      | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | sP3(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),X0,k6_relat_1(k3_relat_1(sK0)),X1,X2) ) ),
    inference(superposition,[],[f23,f72])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | sP3(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (13981)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.47  % (13989)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (13981)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f297,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (~r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (v1_relat_1(X0) => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_wellord1)).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f296,f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f295,f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f122,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f65,f15])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.20/0.50    inference(resolution,[],[f63,f16])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) | ~v1_relat_1(X0) | sK2(X0,X0,k6_relat_1(k3_relat_1(X0))) = k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK2(X0,X0,k6_relat_1(k3_relat_1(X0))))) )),
% 0.20/0.50    inference(resolution,[],[f61,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X2] : (r2_hidden(sK2(X2,X2,k6_relat_1(k3_relat_1(X2))),k3_relat_1(X2)) | r3_wellord1(X2,X2,k6_relat_1(k3_relat_1(X2))) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f58,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X2,X2,k6_relat_1(k3_relat_1(X2))),sK2(X2,X2,k6_relat_1(k3_relat_1(X2)))),X2) | r3_wellord1(X2,X2,k6_relat_1(k3_relat_1(X2))) | r2_hidden(sK2(X2,X2,k6_relat_1(k3_relat_1(X2))),k3_relat_1(X2))) )),
% 0.20/0.50    inference(resolution,[],[f55,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X3,X2,X1,X0) | r2_hidden(X4,k3_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0) | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(X0) | sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0) | r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0) | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_relat_1(X0) != k3_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | sP3(sK2(X1,X0,k6_relat_1(k3_relat_1(X1))),sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),k6_relat_1(k3_relat_1(X1)),X0,X1) | r2_hidden(k4_tarski(sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),sK2(X1,X0,k6_relat_1(k3_relat_1(X1)))),X1) | r3_wellord1(X1,X0,k6_relat_1(k3_relat_1(X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X2) != X0 | k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f45,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f44,f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f43,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f42,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(superposition,[],[f27,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) != k3_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X2) | sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X2,X1,X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | r3_wellord1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f121,f15])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f116,f16])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.20/0.50    inference(superposition,[],[f57,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f15])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.20/0.50    inference(resolution,[],[f64,f16])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) | ~v1_relat_1(X0) | sK1(X0,X0,k6_relat_1(k3_relat_1(X0))) = k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))))) )),
% 0.20/0.50    inference(resolution,[],[f62,f34])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X3] : (r2_hidden(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),k3_relat_1(X3)) | r3_wellord1(X3,X3,k6_relat_1(k3_relat_1(X3))) | ~v1_relat_1(X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f59,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X3] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),sK2(X3,X3,k6_relat_1(k3_relat_1(X3)))),X3) | r3_wellord1(X3,X3,k6_relat_1(k3_relat_1(X3))) | r2_hidden(sK1(X3,X3,k6_relat_1(k3_relat_1(X3))),k3_relat_1(X3))) )),
% 0.20/0.50    inference(resolution,[],[f55,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X3,X2,X1,X0) | r2_hidden(X3,k3_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X1] : (r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK1(X1,X1,k6_relat_1(k3_relat_1(X1)))),k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK2(X1,X1,k6_relat_1(k3_relat_1(X1))))),X1) | r2_hidden(k4_tarski(sK1(X1,X1,k6_relat_1(k3_relat_1(X1))),sK2(X1,X1,k6_relat_1(k3_relat_1(X1)))),X1) | r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(resolution,[],[f55,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X3,X2,X1,X0) | r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f294,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f15])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f124,f35])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f293,f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f126,f15])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f124,f36])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f288])).
% 0.20/0.50  fof(f288,plain,(
% 0.20/0.50    ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.20/0.50    inference(resolution,[],[f86,f217])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ( ! [X0] : (~sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0) | ~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0) | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(X0) | ~sP3(sK2(X0,X0,k6_relat_1(k3_relat_1(X0))),sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),k6_relat_1(k3_relat_1(X0)),X0,X0) | ~r2_hidden(k4_tarski(sK1(X0,X0,k6_relat_1(k3_relat_1(X0))),sK2(X0,X0,k6_relat_1(k3_relat_1(X0)))),X0) | r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_relat_1(X0) != k3_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~sP3(sK2(X1,X0,k6_relat_1(k3_relat_1(X1))),sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),k6_relat_1(k3_relat_1(X1)),X0,X1) | ~r2_hidden(k4_tarski(sK1(X1,X0,k6_relat_1(k3_relat_1(X1))),sK2(X1,X0,k6_relat_1(k3_relat_1(X1)))),X1) | r3_wellord1(X1,X0,k6_relat_1(k3_relat_1(X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X2) != X0 | k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | ~r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f51,f21])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | ~r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f50,f18])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | ~sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | ~r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f49,f20])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_funct_1(k6_relat_1(X0)) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | ~sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | ~r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f48,f17])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k3_relat_1(X1) != X0 | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X2) | ~v2_funct_1(k6_relat_1(X0)) | ~sP3(sK2(X2,X1,k6_relat_1(X0)),sK1(X2,X1,k6_relat_1(X0)),k6_relat_1(X0),X1,X2) | ~r2_hidden(k4_tarski(sK1(X2,X1,k6_relat_1(X0)),sK2(X2,X1,k6_relat_1(X0))),X2) | r3_wellord1(X2,X1,k6_relat_1(X0))) )),
% 0.20/0.50    inference(superposition,[],[f28,f22])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) != k3_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X2) | ~sP3(sK2(X0,X1,X2),sK1(X0,X1,X2),X2,X1,X0) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | r3_wellord1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2,X3] : (sP3(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k6_relat_1(k3_relat_1(sK0)),X2,X3) | ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X3)) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X3)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),X2)) )),
% 0.20/0.50    inference(superposition,[],[f73,f82])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),X0),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),X1) | ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | sP3(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),X0,k6_relat_1(k3_relat_1(sK0)),X1,X2)) )),
% 0.20/0.50    inference(superposition,[],[f23,f72])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | sP3(X4,X3,X2,X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (13981)------------------------------
% 0.20/0.50  % (13981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13981)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (13981)Memory used [KB]: 6396
% 0.20/0.50  % (13981)Time elapsed: 0.076 s
% 0.20/0.50  % (13981)------------------------------
% 0.20/0.50  % (13981)------------------------------
% 0.20/0.50  % (13967)Success in time 0.148 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:20 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 662 expanded)
%              Number of leaves         :    6 ( 121 expanded)
%              Depth                    :   22
%              Number of atoms          :  213 (2890 expanded)
%              Number of equality atoms :   33 ( 466 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(subsumption_resolution,[],[f348,f352])).

fof(f352,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f351,f20])).

fof(f20,plain,(
    k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
             => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f351,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f350,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f350,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f347,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f347,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(resolution,[],[f341,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f341,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    inference(backward_demodulation,[],[f136,f339])).

fof(f339,plain,(
    k1_funct_1(sK2,sK0) = sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)) ),
    inference(subsumption_resolution,[],[f338,f335])).

fof(f335,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f135,f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f135,plain,(
    r2_hidden(k4_tarski(sK0,sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0))),sK2) ),
    inference(backward_demodulation,[],[f129,f133])).

fof(f133,plain,(
    k1_funct_1(k5_relat_1(sK2,sK1),sK0) = sK8(k5_relat_1(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f57,plain,(
    v1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f51,f21])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f35,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = sK8(k5_relat_1(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f131,f19])).

fof(f19,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = sK8(k5_relat_1(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f124,f92])).

fof(f92,plain,(
    v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f90,f21])).

fof(f90,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f60,f22])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k5_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f58,f17])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k5_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f124,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | k1_funct_1(k5_relat_1(sK2,sK1),sK0) = sK8(k5_relat_1(sK2,sK1),sK0) ),
    inference(resolution,[],[f53,f31])).

fof(f53,plain,(
    r2_hidden(k4_tarski(sK0,sK8(k5_relat_1(sK2,sK1),sK0)),k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f46,f19])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f129,plain,(
    r2_hidden(k4_tarski(sK0,sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0))),sK2) ),
    inference(subsumption_resolution,[],[f128,f17])).

fof(f128,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f122,f21])).

fof(f122,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK0,sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0))),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK5(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
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
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f338,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK0) = sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)) ),
    inference(subsumption_resolution,[],[f337,f17])).

fof(f337,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)) ),
    inference(subsumption_resolution,[],[f334,f18])).

fof(f334,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK0) = sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)) ),
    inference(resolution,[],[f135,f31])).

fof(f136,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK1,sK0,k1_funct_1(k5_relat_1(sK2,sK1),sK0)),k1_funct_1(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    inference(backward_demodulation,[],[f127,f133])).

fof(f127,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0)),sK8(k5_relat_1(sK2,sK1),sK0)),sK1) ),
    inference(subsumption_resolution,[],[f126,f17])).

fof(f126,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0)),sK8(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f121,f21])).

fof(f121,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK1,sK0,sK8(k5_relat_1(sK2,sK1),sK0)),sK8(k5_relat_1(sK2,sK1),sK0)),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f41,f35])).

fof(f41,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f348,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f341,f47])).

%------------------------------------------------------------------------------

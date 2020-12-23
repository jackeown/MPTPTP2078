%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0619+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 100 expanded)
%              Number of leaves         :    3 (  18 expanded)
%              Depth                    :   18
%              Number of atoms          :  133 ( 347 expanded)
%              Number of equality atoms :   70 ( 173 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(subsumption_resolution,[],[f272,f12])).

fof(f12,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f272,plain,(
    k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f271,f29])).

fof(f29,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f271,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_tarski(k1_funct_1(sK1,sK0)))
    | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_tarski(k1_funct_1(sK1,sK0)))
    | k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(superposition,[],[f68,f254])).

fof(f254,plain,(
    k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f253,f12])).

fof(f253,plain,
    ( k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(k1_funct_1(sK1,sK0)))
    | k2_relat_1(sK1) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) != X0
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(equality_factoring,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0))
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0))
      | k1_tarski(X0) = k2_relat_1(sK1)
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1)
      | sK2(sK1,k1_tarski(X0)) = X0 ) ),
    inference(superposition,[],[f62,f77])).

fof(f77,plain,(
    ! [X5] :
      ( sK0 = sK4(sK1,k1_tarski(X5))
      | k2_relat_1(sK1) = k1_tarski(X5)
      | sK2(sK1,k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1
      | sK0 = sK4(sK1,X1) ) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f32,f11])).

fof(f11,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f30,f9])).

fof(f9,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(sK4(sK1,X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(resolution,[],[f10,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f10,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

% (28473)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f62,plain,(
    ! [X5] :
      ( sK2(sK1,k1_tarski(X5)) = k1_funct_1(sK1,sK4(sK1,k1_tarski(X5)))
      | k2_relat_1(sK1) = k1_tarski(X5)
      | sK2(sK1,k1_tarski(X5)) = X5 ) ),
    inference(resolution,[],[f34,f27])).

fof(f34,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1),X1)
      | sK2(sK1,X1) = k1_funct_1(sK1,sK4(sK1,X1))
      | k2_relat_1(sK1) = X1 ) ),
    inference(subsumption_resolution,[],[f31,f9])).

fof(f31,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | sK2(sK1,X1) = k1_funct_1(sK1,sK4(sK1,X1))
      | r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1 ) ),
    inference(resolution,[],[f10,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK2(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK1,X0),X0)
      | k1_funct_1(sK1,sK0) != sK2(sK1,X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | sK2(sK1,X1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1 ) ),
    inference(subsumption_resolution,[],[f37,f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_relat_1(sK1)
      | sK2(sK1,X1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1 ) ),
    inference(subsumption_resolution,[],[f35,f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | sK2(sK1,X1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1 ) ),
    inference(superposition,[],[f13,f11])).

fof(f13,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X3) != sK2(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------

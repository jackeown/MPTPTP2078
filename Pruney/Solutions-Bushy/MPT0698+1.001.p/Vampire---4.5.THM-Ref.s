%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0698+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 348 expanded)
%              Number of leaves         :    8 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 (1228 expanded)
%              Number of equality atoms :   45 ( 129 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f103,f56])).

fof(f56,plain,(
    ~ r1_tarski(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f55,plain,(
    sK1(sK0) != sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f24,f21,f22,f30])).

fof(f30,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] : r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_funct_1)).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f103,plain,(
    r1_tarski(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(forward_demodulation,[],[f102,f97])).

fof(f97,plain,(
    k1_tarski(sK1(sK0)) = k10_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f52,f93,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f93,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) ),
    inference(backward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f87,f83])).

fof(f83,plain,(
    k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK1(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f21,f53,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f53,plain,(
    r2_hidden(sK1(sK0),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f21,f22,f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,(
    k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f84,f72])).

fof(f72,plain,(
    k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f24,f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,(
    k1_tarski(k1_funct_1(sK0,sK2(sK0))) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f21,f54,f40])).

fof(f54,plain,(
    r2_hidden(sK2(sK0),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f21,f22,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))) ),
    inference(backward_demodulation,[],[f60,f87])).

fof(f60,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f21,f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f58,plain,(
    r2_hidden(k1_funct_1(sK0,sK1(sK0)),k2_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f53,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK0,k11_relat_1(sK0,X0)),k1_tarski(X0)) ),
    inference(superposition,[],[f23,f51])).

fof(f51,plain,(
    ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f23,plain,(
    ! [X1] : r1_tarski(k10_relat_1(sK0,k9_relat_1(sK0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,(
    r1_tarski(k10_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_tarski(sK2(sK0))) ),
    inference(superposition,[],[f52,f92])).

%------------------------------------------------------------------------------

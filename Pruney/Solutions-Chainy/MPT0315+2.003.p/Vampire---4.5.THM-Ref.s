%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:09 EST 2020

% Result     : Theorem 6.22s
% Output     : Refutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 176 expanded)
%              Number of leaves         :   13 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  161 ( 400 expanded)
%              Number of equality atoms :   43 (  92 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5733,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f4132,f5373,f478])).

fof(f478,plain,(
    ! [X88,X87,X89,X86] :
      ( ~ r1_xboole_0(X89,k2_zfmisc_1(X86,k2_xboole_0(X87,X88)))
      | r1_xboole_0(X89,k2_zfmisc_1(X86,X87)) ) ),
    inference(superposition,[],[f39,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f5373,plain,(
    ! [X0] : r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f5313,f2375])).

fof(f2375,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(trivial_inequality_removal,[],[f2374])).

fof(f2374,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f2373,f56])).

fof(f56,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2373,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
      | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f2353,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f50,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f2353,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,X2),X4)
      | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f614,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f614,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3)
      | r1_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3)) ) ),
    inference(superposition,[],[f52,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f37,f24,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f5313,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f61,f5291,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK3)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f42,f20])).

fof(f20,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f5291,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f4135,f2206])).

fof(f2206,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(trivial_inequality_removal,[],[f2205])).

fof(f2205,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f2204,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2204,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(X4,k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(forward_demodulation,[],[f2186,f59])).

fof(f2186,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(X4,k4_xboole_0(X2,X2))
      | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f571,f29])).

fof(f571,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ) ),
    inference(superposition,[],[f52,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f38,f24,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4135,plain,(
    ! [X0,X1] : ~ r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,sK0),sK2),k2_zfmisc_1(k2_xboole_0(sK1,X1),sK3)) ),
    inference(unit_resulting_resolution,[],[f4131,f417])).

fof(f417,plain,(
    ! [X85,X83,X84,X82] :
      ( ~ r1_xboole_0(X85,k2_zfmisc_1(k2_xboole_0(X82,X84),X83))
      | r1_xboole_0(X85,k2_zfmisc_1(X82,X83)) ) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4131,plain,(
    ! [X0] : ~ r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,sK0),sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(superposition,[],[f4109,f35])).

fof(f4109,plain,(
    ! [X0] : ~ r1_xboole_0(k2_xboole_0(X0,k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f63,f3880,f1568])).

fof(f1568,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,k2_zfmisc_1(sK1,sK3))
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f317,f85])).

fof(f85,plain,(
    ! [X0] : ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0)) ),
    inference(unit_resulting_resolution,[],[f21,f39])).

fof(f21,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f317,plain,(
    ! [X64,X62,X65,X63] :
      ( r1_xboole_0(X65,k2_xboole_0(X63,X64))
      | ~ r1_xboole_0(X62,X64)
      | ~ r1_tarski(X65,X62)
      | ~ r1_xboole_0(X62,X63) ) ),
    inference(resolution,[],[f41,f42])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3880,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f3873])).

fof(f3873,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X0))
      | r1_tarski(X0,k2_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f1460,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1460,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK4(X2,k2_xboole_0(X3,X4)),X4)
      | r1_tarski(X2,k2_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f151,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f151,plain,(
    ! [X4,X5,X3] :
      ( ~ sP6(sK4(X3,k2_xboole_0(X4,X5)),X5,X4)
      | r1_tarski(X3,k2_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f58,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f27,f26])).

fof(f4132,plain,(
    ! [X1] : ~ r1_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(X1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(superposition,[],[f4109,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:17:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (5583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (5574)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (5565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (5564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (5566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (5573)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (5567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.53  % (5572)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (5561)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.54  % (5576)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.54  % (5561)Refutation not found, incomplete strategy% (5561)------------------------------
% 1.28/0.54  % (5561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (5561)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (5561)Memory used [KB]: 1663
% 1.28/0.54  % (5561)Time elapsed: 0.127 s
% 1.28/0.54  % (5561)------------------------------
% 1.28/0.54  % (5561)------------------------------
% 1.28/0.54  % (5590)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.54  % (5568)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.54  % (5575)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (5562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (5588)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.54  % (5582)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (5589)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.54  % (5569)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.54  % (5580)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (5587)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (5581)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (5563)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.55  % (5571)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (5584)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.55  % (5571)Refutation not found, incomplete strategy% (5571)------------------------------
% 1.43/0.55  % (5571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (5571)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (5571)Memory used [KB]: 10618
% 1.43/0.55  % (5571)Time elapsed: 0.139 s
% 1.43/0.55  % (5571)------------------------------
% 1.43/0.55  % (5571)------------------------------
% 1.43/0.55  % (5577)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.56  % (5579)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.56  % (5570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.57  % (5585)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.58  % (5586)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.58  % (5578)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.59  % (5578)Refutation not found, incomplete strategy% (5578)------------------------------
% 1.43/0.59  % (5578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.60  % (5578)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.60  
% 1.43/0.60  % (5578)Memory used [KB]: 10618
% 1.43/0.60  % (5578)Time elapsed: 0.182 s
% 1.43/0.60  % (5578)------------------------------
% 1.43/0.60  % (5578)------------------------------
% 2.05/0.68  % (5591)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.45/0.71  % (5592)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.04/0.77  % (5593)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.57/0.86  % (5566)Time limit reached!
% 3.57/0.86  % (5566)------------------------------
% 3.57/0.86  % (5566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.57/0.86  % (5566)Termination reason: Time limit
% 3.57/0.86  
% 3.57/0.86  % (5566)Memory used [KB]: 10874
% 3.57/0.86  % (5566)Time elapsed: 0.410 s
% 3.57/0.86  % (5566)------------------------------
% 3.57/0.86  % (5566)------------------------------
% 4.16/0.94  % (5573)Time limit reached!
% 4.16/0.94  % (5573)------------------------------
% 4.16/0.94  % (5573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.94  % (5562)Time limit reached!
% 4.16/0.94  % (5562)------------------------------
% 4.16/0.94  % (5562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.94  % (5562)Termination reason: Time limit
% 4.16/0.94  
% 4.16/0.94  % (5562)Memory used [KB]: 8699
% 4.16/0.94  % (5562)Time elapsed: 0.524 s
% 4.16/0.94  % (5562)------------------------------
% 4.16/0.94  % (5562)------------------------------
% 4.16/0.95  % (5573)Termination reason: Time limit
% 4.16/0.95  
% 4.16/0.95  % (5573)Memory used [KB]: 9083
% 4.16/0.95  % (5573)Time elapsed: 0.518 s
% 4.16/0.95  % (5573)------------------------------
% 4.16/0.95  % (5573)------------------------------
% 4.54/0.98  % (5594)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.54/1.02  % (5568)Time limit reached!
% 4.54/1.02  % (5568)------------------------------
% 4.54/1.02  % (5568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.03  % (5589)Time limit reached!
% 4.54/1.03  % (5589)------------------------------
% 4.54/1.03  % (5589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.03  % (5577)Time limit reached!
% 4.54/1.03  % (5577)------------------------------
% 4.54/1.03  % (5577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.03  % (5568)Termination reason: Time limit
% 4.54/1.03  
% 4.54/1.03  % (5568)Memory used [KB]: 9722
% 4.54/1.03  % (5568)Time elapsed: 0.607 s
% 4.54/1.03  % (5568)------------------------------
% 4.54/1.03  % (5568)------------------------------
% 4.54/1.03  % (5577)Termination reason: Time limit
% 4.54/1.03  % (5577)Termination phase: Saturation
% 4.54/1.03  
% 4.54/1.03  % (5577)Memory used [KB]: 18805
% 4.54/1.03  % (5577)Time elapsed: 0.600 s
% 4.54/1.03  % (5577)------------------------------
% 4.54/1.03  % (5577)------------------------------
% 4.54/1.03  % (5589)Termination reason: Time limit
% 4.54/1.03  
% 4.54/1.03  % (5589)Memory used [KB]: 10106
% 4.54/1.03  % (5589)Time elapsed: 0.622 s
% 4.54/1.03  % (5589)------------------------------
% 4.54/1.03  % (5589)------------------------------
% 5.62/1.08  % (5595)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.62/1.12  % (5598)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.62/1.12  % (5597)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.95/1.13  % (5596)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.95/1.13  % (5599)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.22/1.22  % (5585)Refutation found. Thanks to Tanya!
% 6.22/1.22  % SZS status Theorem for theBenchmark
% 6.22/1.22  % SZS output start Proof for theBenchmark
% 6.22/1.22  fof(f5733,plain,(
% 6.22/1.22    $false),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f4132,f5373,f478])).
% 6.22/1.22  fof(f478,plain,(
% 6.22/1.22    ( ! [X88,X87,X89,X86] : (~r1_xboole_0(X89,k2_zfmisc_1(X86,k2_xboole_0(X87,X88))) | r1_xboole_0(X89,k2_zfmisc_1(X86,X87))) )),
% 6.22/1.22    inference(superposition,[],[f39,f36])).
% 6.22/1.22  fof(f36,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 6.22/1.22    inference(cnf_transformation,[],[f11])).
% 6.22/1.22  fof(f11,axiom,(
% 6.22/1.22    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 6.22/1.22  fof(f39,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f17])).
% 6.22/1.22  fof(f17,plain,(
% 6.22/1.22    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.22/1.22    inference(ennf_transformation,[],[f8])).
% 6.22/1.22  fof(f8,axiom,(
% 6.22/1.22    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 6.22/1.22  fof(f5373,plain,(
% 6.22/1.22    ( ! [X0] : (r1_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X0))) )),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f5313,f2375])).
% 6.22/1.22  fof(f2375,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(trivial_inequality_removal,[],[f2374])).
% 6.22/1.22  fof(f2374,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(forward_demodulation,[],[f2373,f56])).
% 6.22/1.22  fof(f56,plain,(
% 6.22/1.22    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.22/1.22    inference(equality_resolution,[],[f33])).
% 6.22/1.22  fof(f33,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f10])).
% 6.22/1.22  fof(f10,axiom,(
% 6.22/1.22    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.22/1.22  fof(f2373,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4) | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(forward_demodulation,[],[f2353,f59])).
% 6.22/1.22  fof(f59,plain,(
% 6.22/1.22    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 6.22/1.22    inference(backward_demodulation,[],[f50,f23])).
% 6.22/1.22  fof(f23,plain,(
% 6.22/1.22    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.22/1.22    inference(cnf_transformation,[],[f5])).
% 6.22/1.22  fof(f5,axiom,(
% 6.22/1.22    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 6.22/1.22  fof(f50,plain,(
% 6.22/1.22    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.22/1.22    inference(definition_unfolding,[],[f22,f24])).
% 6.22/1.22  fof(f24,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.22/1.22    inference(cnf_transformation,[],[f6])).
% 6.22/1.22  fof(f6,axiom,(
% 6.22/1.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.22/1.22  fof(f22,plain,(
% 6.22/1.22    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f4])).
% 6.22/1.22  fof(f4,axiom,(
% 6.22/1.22    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 6.22/1.22  fof(f2353,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,X2),X4) | r1_xboole_0(k2_zfmisc_1(X2,X4),k2_zfmisc_1(X3,X4)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(superposition,[],[f614,f29])).
% 6.22/1.22  fof(f29,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f9])).
% 6.22/1.22  fof(f9,axiom,(
% 6.22/1.22    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 6.22/1.22  fof(f614,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3) | r1_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3))) )),
% 6.22/1.22    inference(superposition,[],[f52,f54])).
% 6.22/1.22  fof(f54,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 6.22/1.22    inference(definition_unfolding,[],[f37,f24,f24])).
% 6.22/1.22  fof(f37,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 6.22/1.22    inference(cnf_transformation,[],[f12])).
% 6.22/1.22  fof(f12,axiom,(
% 6.22/1.22    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 6.22/1.22  fof(f52,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(definition_unfolding,[],[f30,f24])).
% 6.22/1.22  fof(f30,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f3])).
% 6.22/1.22  fof(f3,axiom,(
% 6.22/1.22    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 6.22/1.22  fof(f5313,plain,(
% 6.22/1.22    r1_xboole_0(sK0,sK1)),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f61,f5291,f125])).
% 6.22/1.22  fof(f125,plain,(
% 6.22/1.22    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK3) | r1_xboole_0(sK0,sK1)) )),
% 6.22/1.22    inference(resolution,[],[f42,f20])).
% 6.22/1.22  fof(f20,plain,(
% 6.22/1.22    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 6.22/1.22    inference(cnf_transformation,[],[f15])).
% 6.22/1.22  fof(f15,plain,(
% 6.22/1.22    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 6.22/1.22    inference(ennf_transformation,[],[f14])).
% 6.22/1.22  fof(f14,negated_conjecture,(
% 6.22/1.22    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 6.22/1.22    inference(negated_conjecture,[],[f13])).
% 6.22/1.22  fof(f13,conjecture,(
% 6.22/1.22    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 6.22/1.22  fof(f42,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f19])).
% 6.22/1.22  fof(f19,plain,(
% 6.22/1.22    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 6.22/1.22    inference(flattening,[],[f18])).
% 6.22/1.22  fof(f18,plain,(
% 6.22/1.22    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.22/1.22    inference(ennf_transformation,[],[f7])).
% 6.22/1.22  fof(f7,axiom,(
% 6.22/1.22    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 6.22/1.22  fof(f5291,plain,(
% 6.22/1.22    ~r1_xboole_0(sK2,sK3)),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f4135,f2206])).
% 6.22/1.22  fof(f2206,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(trivial_inequality_removal,[],[f2205])).
% 6.22/1.22  fof(f2205,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(forward_demodulation,[],[f2204,f55])).
% 6.22/1.22  fof(f55,plain,(
% 6.22/1.22    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.22/1.22    inference(equality_resolution,[],[f34])).
% 6.22/1.22  fof(f34,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f10])).
% 6.22/1.22  fof(f2204,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(X4,k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(forward_demodulation,[],[f2186,f59])).
% 6.22/1.22  fof(f2186,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (k1_xboole_0 != k2_zfmisc_1(X4,k4_xboole_0(X2,X2)) | r1_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X4,X3)) | ~r1_xboole_0(X2,X3)) )),
% 6.22/1.22    inference(superposition,[],[f571,f29])).
% 6.22/1.22  fof(f571,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r1_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) )),
% 6.22/1.22    inference(superposition,[],[f52,f53])).
% 6.22/1.22  fof(f53,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 6.22/1.22    inference(definition_unfolding,[],[f38,f24,f24])).
% 6.22/1.22  fof(f38,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 6.22/1.22    inference(cnf_transformation,[],[f12])).
% 6.22/1.22  fof(f4135,plain,(
% 6.22/1.22    ( ! [X0,X1] : (~r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,sK0),sK2),k2_zfmisc_1(k2_xboole_0(sK1,X1),sK3))) )),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f4131,f417])).
% 6.22/1.22  fof(f417,plain,(
% 6.22/1.22    ( ! [X85,X83,X84,X82] : (~r1_xboole_0(X85,k2_zfmisc_1(k2_xboole_0(X82,X84),X83)) | r1_xboole_0(X85,k2_zfmisc_1(X82,X83))) )),
% 6.22/1.22    inference(superposition,[],[f39,f35])).
% 6.22/1.22  fof(f35,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 6.22/1.22    inference(cnf_transformation,[],[f11])).
% 6.22/1.22  fof(f4131,plain,(
% 6.22/1.22    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(k2_xboole_0(X0,sK0),sK2),k2_zfmisc_1(sK1,sK3))) )),
% 6.22/1.22    inference(superposition,[],[f4109,f35])).
% 6.22/1.22  fof(f4109,plain,(
% 6.22/1.22    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(X0,k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK1,sK3))) )),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f63,f3880,f1568])).
% 6.22/1.22  fof(f1568,plain,(
% 6.22/1.22    ( ! [X0,X1] : (~r1_xboole_0(X0,k2_zfmisc_1(sK1,sK3)) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),X0) | ~r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(resolution,[],[f317,f85])).
% 6.22/1.22  fof(f85,plain,(
% 6.22/1.22    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0))) )),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f21,f39])).
% 6.22/1.22  fof(f21,plain,(
% 6.22/1.22    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 6.22/1.22    inference(cnf_transformation,[],[f15])).
% 6.22/1.22  fof(f317,plain,(
% 6.22/1.22    ( ! [X64,X62,X65,X63] : (r1_xboole_0(X65,k2_xboole_0(X63,X64)) | ~r1_xboole_0(X62,X64) | ~r1_tarski(X65,X62) | ~r1_xboole_0(X62,X63)) )),
% 6.22/1.22    inference(resolution,[],[f41,f42])).
% 6.22/1.22  fof(f41,plain,(
% 6.22/1.22    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f17])).
% 6.22/1.22  fof(f3880,plain,(
% 6.22/1.22    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 6.22/1.22    inference(duplicate_literal_removal,[],[f3873])).
% 6.22/1.22  fof(f3873,plain,(
% 6.22/1.22    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0)) | r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 6.22/1.22    inference(resolution,[],[f1460,f26])).
% 6.22/1.22  fof(f26,plain,(
% 6.22/1.22    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f16])).
% 6.22/1.22  fof(f16,plain,(
% 6.22/1.22    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.22/1.22    inference(ennf_transformation,[],[f1])).
% 6.22/1.22  fof(f1,axiom,(
% 6.22/1.22    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.22/1.22  fof(f1460,plain,(
% 6.22/1.22    ( ! [X4,X2,X3] : (~r2_hidden(sK4(X2,k2_xboole_0(X3,X4)),X4) | r1_tarski(X2,k2_xboole_0(X3,X4))) )),
% 6.22/1.22    inference(resolution,[],[f151,f44])).
% 6.22/1.22  fof(f44,plain,(
% 6.22/1.22    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f2])).
% 6.22/1.22  fof(f2,axiom,(
% 6.22/1.22    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.22/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 6.22/1.22  fof(f151,plain,(
% 6.22/1.22    ( ! [X4,X5,X3] : (~sP6(sK4(X3,k2_xboole_0(X4,X5)),X5,X4) | r1_tarski(X3,k2_xboole_0(X4,X5))) )),
% 6.22/1.22    inference(resolution,[],[f58,f27])).
% 6.22/1.22  fof(f27,plain,(
% 6.22/1.22    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f16])).
% 6.22/1.22  fof(f58,plain,(
% 6.22/1.22    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~sP6(X3,X1,X0)) )),
% 6.22/1.22    inference(equality_resolution,[],[f46])).
% 6.22/1.22  fof(f46,plain,(
% 6.22/1.22    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 6.22/1.22    inference(cnf_transformation,[],[f2])).
% 6.22/1.22  fof(f63,plain,(
% 6.22/1.22    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.22/1.22    inference(unit_resulting_resolution,[],[f23,f28])).
% 6.22/1.22  fof(f28,plain,(
% 6.22/1.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 6.22/1.22    inference(cnf_transformation,[],[f9])).
% 6.22/1.22  fof(f61,plain,(
% 6.22/1.22    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.22/1.22    inference(duplicate_literal_removal,[],[f60])).
% 6.22/1.22  fof(f60,plain,(
% 6.22/1.22    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 6.22/1.22    inference(resolution,[],[f27,f26])).
% 6.22/1.22  fof(f4132,plain,(
% 6.22/1.22    ( ! [X1] : (~r1_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(X1,sK2)),k2_zfmisc_1(sK1,sK3))) )),
% 6.22/1.22    inference(superposition,[],[f4109,f36])).
% 6.22/1.22  % SZS output end Proof for theBenchmark
% 6.22/1.22  % (5585)------------------------------
% 6.22/1.22  % (5585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.22/1.22  % (5585)Termination reason: Refutation
% 6.22/1.22  
% 6.22/1.22  % (5585)Memory used [KB]: 13304
% 6.22/1.22  % (5585)Time elapsed: 0.796 s
% 6.22/1.22  % (5585)------------------------------
% 6.22/1.22  % (5585)------------------------------
% 6.22/1.22  % (5560)Success in time 0.859 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:22 EST 2020

% Result     : Theorem 51.22s
% Output     : Refutation 52.00s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 512 expanded)
%              Number of leaves         :   11 ( 125 expanded)
%              Depth                    :   24
%              Number of atoms          :  165 (1174 expanded)
%              Number of equality atoms :   30 ( 162 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70080,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70080,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f69256,f46])).

fof(f69256,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f69204,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f69204,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK1) ),
    inference(subsumption_resolution,[],[f69000,f31717])).

fof(f31717,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X0),X1) ),
    inference(resolution,[],[f31526,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f31526,plain,(
    ! [X83,X82] : r1_tarski(X82,k2_xboole_0(X82,X83)) ),
    inference(forward_demodulation,[],[f29292,f29428])).

fof(f29428,plain,(
    ! [X6] : k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))) = X6 ),
    inference(subsumption_resolution,[],[f29245,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f29245,plain,(
    ! [X6] :
      ( ~ r1_tarski(k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))),X6)
      | k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))) = X6 ) ),
    inference(resolution,[],[f29181,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f29181,plain,(
    ! [X74] : r1_tarski(X74,k6_subset_1(X74,k6_subset_1(sK0,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f534,f46])).

fof(f534,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k6_subset_1(X4,k6_subset_1(sK0,k2_relat_1(sK2))),X3)
      | r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f42,f244])).

fof(f244,plain,(
    ! [X2] : k2_xboole_0(k6_subset_1(sK0,k2_relat_1(sK2)),X2) = X2 ),
    inference(resolution,[],[f170,f38])).

fof(f170,plain,(
    ! [X3] : r1_tarski(k6_subset_1(sK0,k2_relat_1(sK2)),X3) ),
    inference(resolution,[],[f161,f43])).

fof(f161,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0)) ),
    inference(resolution,[],[f96,f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X1),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(sK2),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f29292,plain,(
    ! [X83,X82] : r1_tarski(X82,k6_subset_1(k2_xboole_0(X82,X83),k6_subset_1(sK0,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f29181,f33])).

fof(f69000,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_subset_1(sK0,sK0),X0)
      | ~ r1_tarski(k2_xboole_0(sK1,X0),sK1) ) ),
    inference(superposition,[],[f74,f68859])).

fof(f68859,plain,(
    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f64682,f65443])).

fof(f65443,plain,(
    ! [X216] : k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X216,X216)) ),
    inference(superposition,[],[f378,f58053])).

fof(f58053,plain,(
    ! [X128,X129] : k10_relat_1(sK2,k6_subset_1(X129,X129)) = k6_subset_1(X128,X128) ),
    inference(resolution,[],[f32070,f4029])).

fof(f4029,plain,(
    ! [X23,X22] : r1_tarski(k10_relat_1(sK2,k6_subset_1(X22,X22)),X23) ),
    inference(resolution,[],[f511,f46])).

fof(f511,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,X5),X8),k2_xboole_0(k10_relat_1(sK2,X6),X7))
      | r1_tarski(k10_relat_1(sK2,k6_subset_1(X5,X6)),X7) ) ),
    inference(resolution,[],[f132,f33])).

fof(f132,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k10_relat_1(sK2,X4),k2_xboole_0(k10_relat_1(sK2,X5),X6))
      | r1_tarski(k10_relat_1(sK2,k6_subset_1(X4,X5)),X6) ) ),
    inference(superposition,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f26,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f32070,plain,(
    ! [X163,X164] :
      ( ~ r1_tarski(X163,k6_subset_1(X164,X164))
      | k6_subset_1(X164,X164) = X163 ) ),
    inference(resolution,[],[f31717,f37])).

fof(f378,plain,(
    ! [X2] : k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2))) ),
    inference(subsumption_resolution,[],[f377,f26])).

fof(f377,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2))) ) ),
    inference(subsumption_resolution,[],[f371,f25])).

fof(f371,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2))) ) ),
    inference(resolution,[],[f350,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f350,plain,(
    ! [X3] : r1_tarski(k6_subset_1(sK0,X3),k2_relat_1(sK2)) ),
    inference(resolution,[],[f336,f43])).

fof(f336,plain,(
    ! [X2] : r1_tarski(sK0,k2_xboole_0(X2,k2_relat_1(sK2))) ),
    inference(resolution,[],[f98,f44])).

fof(f98,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK2),X4),X5)
      | r1_tarski(sK0,k2_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f60,f42])).

fof(f64682,plain,(
    ! [X26] : k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X26,X26)) ),
    inference(superposition,[],[f378,f58048])).

fof(f58048,plain,(
    ! [X121] : k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k6_subset_1(X121,X121) ),
    inference(resolution,[],[f32070,f650])).

fof(f650,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0) ),
    inference(resolution,[],[f402,f132])).

fof(f402,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0)) ),
    inference(resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X1),X0)
      | r1_tarski(k10_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f67,f33])).

fof(f67,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK1),X1)
      | r1_tarski(k10_relat_1(sK2,sK0),X1) ) ),
    inference(resolution,[],[f27,f31])).

fof(f27,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k6_subset_1(sK0,X4),X5)
      | ~ r1_tarski(k2_xboole_0(X4,X5),sK1) ) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f29,f31])).

fof(f29,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (22272)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (22288)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (22264)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (22267)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (22280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (22283)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (22275)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (22262)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (22261)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (22260)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (22263)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (22261)Refutation not found, incomplete strategy% (22261)------------------------------
% 0.22/0.53  % (22261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22261)Memory used [KB]: 1663
% 0.22/0.53  % (22261)Time elapsed: 0.113 s
% 0.22/0.53  % (22261)------------------------------
% 0.22/0.53  % (22261)------------------------------
% 0.22/0.53  % (22274)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (22287)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (22265)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (22266)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22282)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (22285)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (22279)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (22286)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (22271)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (22277)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (22289)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (22278)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (22276)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (22269)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (22281)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (22270)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (22284)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (22268)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (22273)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.16/0.67  % (22263)Refutation not found, incomplete strategy% (22263)------------------------------
% 2.16/0.67  % (22263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (22263)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.68  
% 2.16/0.68  % (22263)Memory used [KB]: 6140
% 2.16/0.68  % (22263)Time elapsed: 0.256 s
% 2.16/0.68  % (22263)------------------------------
% 2.16/0.68  % (22263)------------------------------
% 2.16/0.69  % (22290)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.16/0.71  % (22260)Refutation not found, incomplete strategy% (22260)------------------------------
% 2.16/0.71  % (22260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (22260)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (22260)Memory used [KB]: 1663
% 2.16/0.71  % (22260)Time elapsed: 0.271 s
% 2.16/0.71  % (22260)------------------------------
% 2.16/0.71  % (22260)------------------------------
% 3.34/0.81  % (22284)Time limit reached!
% 3.34/0.81  % (22284)------------------------------
% 3.34/0.81  % (22284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.81  % (22284)Termination reason: Time limit
% 3.34/0.81  % (22284)Termination phase: Saturation
% 3.34/0.81  
% 3.34/0.81  % (22284)Memory used [KB]: 12665
% 3.34/0.81  % (22284)Time elapsed: 0.400 s
% 3.34/0.81  % (22284)------------------------------
% 3.34/0.81  % (22284)------------------------------
% 3.34/0.81  % (22262)Time limit reached!
% 3.34/0.81  % (22262)------------------------------
% 3.34/0.81  % (22262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.82  % (22291)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.34/0.84  % (22262)Termination reason: Time limit
% 3.34/0.84  % (22262)Termination phase: Saturation
% 3.34/0.84  
% 3.34/0.84  % (22262)Memory used [KB]: 7803
% 3.34/0.84  % (22262)Time elapsed: 0.400 s
% 3.34/0.84  % (22262)------------------------------
% 3.34/0.84  % (22262)------------------------------
% 3.97/0.89  % (22292)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.97/0.89  % (22292)Refutation not found, incomplete strategy% (22292)------------------------------
% 3.97/0.89  % (22292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.90  % (22292)Termination reason: Refutation not found, incomplete strategy
% 3.97/0.90  
% 3.97/0.90  % (22292)Memory used [KB]: 6140
% 3.97/0.90  % (22292)Time elapsed: 0.129 s
% 3.97/0.90  % (22292)------------------------------
% 3.97/0.90  % (22292)------------------------------
% 4.44/0.94  % (22266)Time limit reached!
% 4.44/0.94  % (22266)------------------------------
% 4.44/0.94  % (22266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.94  % (22266)Termination reason: Time limit
% 4.44/0.94  
% 4.44/0.94  % (22266)Memory used [KB]: 14967
% 4.44/0.94  % (22266)Time elapsed: 0.501 s
% 4.44/0.94  % (22266)------------------------------
% 4.44/0.94  % (22266)------------------------------
% 4.44/0.95  % (22293)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.44/0.95  % (22274)Time limit reached!
% 4.44/0.95  % (22274)------------------------------
% 4.44/0.95  % (22274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.97  % (22274)Termination reason: Time limit
% 4.44/0.97  
% 4.44/0.97  % (22274)Memory used [KB]: 4605
% 4.44/0.97  % (22274)Time elapsed: 0.508 s
% 4.44/0.97  % (22274)------------------------------
% 4.44/0.97  % (22274)------------------------------
% 4.44/0.97  % (22294)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.44/0.99  % (22289)Time limit reached!
% 4.44/0.99  % (22289)------------------------------
% 4.44/0.99  % (22289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.44/0.99  % (22289)Termination reason: Time limit
% 4.44/0.99  % (22289)Termination phase: Saturation
% 4.44/0.99  
% 4.44/0.99  % (22289)Memory used [KB]: 1918
% 4.44/0.99  % (22289)Time elapsed: 0.500 s
% 4.44/0.99  % (22289)------------------------------
% 4.44/0.99  % (22289)------------------------------
% 5.03/1.03  % (22267)Time limit reached!
% 5.03/1.03  % (22267)------------------------------
% 5.03/1.03  % (22267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.03  % (22295)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.03/1.03  % (22267)Termination reason: Time limit
% 5.03/1.03  
% 5.03/1.03  % (22267)Memory used [KB]: 8571
% 5.03/1.03  % (22267)Time elapsed: 0.619 s
% 5.03/1.03  % (22267)------------------------------
% 5.03/1.03  % (22267)------------------------------
% 5.03/1.07  % (22296)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.47/1.11  % (22297)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.47/1.12  % (22298)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.41/1.18  % (22299)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.07/1.41  % (22287)Time limit reached!
% 8.07/1.41  % (22287)------------------------------
% 8.07/1.41  % (22287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.41  % (22287)Termination reason: Time limit
% 8.07/1.41  
% 8.07/1.41  % (22287)Memory used [KB]: 9722
% 8.07/1.41  % (22287)Time elapsed: 1.002 s
% 8.07/1.41  % (22287)------------------------------
% 8.07/1.41  % (22287)------------------------------
% 8.07/1.43  % (22272)Time limit reached!
% 8.07/1.43  % (22272)------------------------------
% 8.07/1.43  % (22272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.45  % (22272)Termination reason: Time limit
% 8.07/1.45  % (22272)Termination phase: Saturation
% 8.07/1.45  
% 8.07/1.45  % (22272)Memory used [KB]: 11129
% 8.07/1.45  % (22272)Time elapsed: 1.0000 s
% 8.07/1.45  % (22272)------------------------------
% 8.07/1.45  % (22272)------------------------------
% 9.22/1.54  % (22300)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.22/1.59  % (22296)Time limit reached!
% 9.22/1.59  % (22296)------------------------------
% 9.22/1.59  % (22296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.22/1.59  % (22296)Termination reason: Time limit
% 9.22/1.59  
% 9.22/1.59  % (22296)Memory used [KB]: 16886
% 9.22/1.59  % (22296)Time elapsed: 0.609 s
% 9.22/1.59  % (22296)------------------------------
% 9.22/1.59  % (22296)------------------------------
% 9.22/1.59  % (22301)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 10.54/1.72  % (22265)Time limit reached!
% 10.54/1.72  % (22265)------------------------------
% 10.54/1.72  % (22265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.72  % (22265)Termination reason: Time limit
% 10.54/1.72  
% 10.54/1.72  % (22265)Memory used [KB]: 7547
% 10.54/1.72  % (22265)Time elapsed: 1.306 s
% 10.54/1.72  % (22265)------------------------------
% 10.54/1.72  % (22265)------------------------------
% 10.54/1.75  % (22302)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.54/1.75  % (22276)Time limit reached!
% 10.54/1.75  % (22276)------------------------------
% 10.54/1.75  % (22276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.54/1.75  % (22276)Termination reason: Time limit
% 10.54/1.75  
% 10.54/1.75  % (22276)Memory used [KB]: 18933
% 10.54/1.75  % (22276)Time elapsed: 1.335 s
% 10.54/1.75  % (22276)------------------------------
% 10.54/1.75  % (22276)------------------------------
% 11.56/1.85  % (22303)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.56/1.87  % (22299)Time limit reached!
% 11.56/1.87  % (22299)------------------------------
% 11.56/1.87  % (22299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.56/1.87  % (22299)Termination reason: Time limit
% 11.56/1.87  % (22299)Termination phase: Saturation
% 11.56/1.87  
% 11.56/1.87  % (22299)Memory used [KB]: 13816
% 11.56/1.87  % (22299)Time elapsed: 0.803 s
% 11.56/1.87  % (22299)------------------------------
% 11.56/1.87  % (22299)------------------------------
% 11.56/1.88  % (22304)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.71/2.01  % (22305)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 12.71/2.02  % (22286)Time limit reached!
% 12.71/2.02  % (22286)------------------------------
% 12.71/2.02  % (22286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.02  % (22286)Termination reason: Time limit
% 12.71/2.02  
% 12.71/2.02  % (22286)Memory used [KB]: 19061
% 12.71/2.02  % (22286)Time elapsed: 1.613 s
% 12.71/2.02  % (22286)------------------------------
% 12.71/2.02  % (22286)------------------------------
% 13.73/2.15  % (22303)Time limit reached!
% 13.73/2.15  % (22303)------------------------------
% 13.73/2.15  % (22303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.73/2.15  % (22303)Termination reason: Time limit
% 13.73/2.15  
% 13.73/2.15  % (22303)Memory used [KB]: 13560
% 13.73/2.15  % (22303)Time elapsed: 0.418 s
% 13.73/2.15  % (22303)------------------------------
% 13.73/2.15  % (22303)------------------------------
% 13.73/2.17  % (22306)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 13.73/2.21  % (22280)Time limit reached!
% 13.73/2.21  % (22280)------------------------------
% 13.73/2.21  % (22280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.73/2.21  % (22280)Termination reason: Time limit
% 13.73/2.21  % (22280)Termination phase: Saturation
% 13.73/2.21  
% 13.73/2.21  % (22280)Memory used [KB]: 23794
% 13.73/2.21  % (22280)Time elapsed: 1.800 s
% 13.73/2.21  % (22280)------------------------------
% 13.73/2.21  % (22280)------------------------------
% 14.71/2.28  % (22307)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 15.25/2.32  % (22305)Time limit reached!
% 15.25/2.32  % (22305)------------------------------
% 15.25/2.32  % (22305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.25/2.32  % (22305)Termination reason: Time limit
% 15.25/2.32  
% 15.25/2.32  % (22305)Memory used [KB]: 6268
% 15.25/2.32  % (22305)Time elapsed: 0.423 s
% 15.25/2.32  % (22305)------------------------------
% 15.25/2.32  % (22305)------------------------------
% 15.25/2.34  % (22308)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 16.18/2.49  % (22309)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 16.88/2.57  % (22306)Time limit reached!
% 16.88/2.57  % (22306)------------------------------
% 16.88/2.57  % (22306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.88/2.57  % (22306)Termination reason: Time limit
% 16.88/2.57  % (22306)Termination phase: Saturation
% 16.88/2.57  
% 16.88/2.57  % (22306)Memory used [KB]: 11257
% 16.88/2.57  % (22306)Time elapsed: 0.500 s
% 16.88/2.57  % (22306)------------------------------
% 16.88/2.57  % (22306)------------------------------
% 16.88/2.57  % (22307)Time limit reached!
% 16.88/2.57  % (22307)------------------------------
% 16.88/2.57  % (22307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.88/2.57  % (22307)Termination reason: Time limit
% 16.88/2.57  
% 16.88/2.57  % (22307)Memory used [KB]: 8315
% 16.88/2.57  % (22307)Time elapsed: 0.403 s
% 16.88/2.57  % (22307)------------------------------
% 16.88/2.57  % (22307)------------------------------
% 18.32/2.70  % (22310)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.73/2.80  % (22309)Time limit reached!
% 18.73/2.80  % (22309)------------------------------
% 18.73/2.80  % (22309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.73/2.80  % (22309)Termination reason: Time limit
% 18.73/2.80  % (22309)Termination phase: Saturation
% 18.73/2.80  
% 18.73/2.80  % (22309)Memory used [KB]: 3709
% 18.73/2.80  % (22309)Time elapsed: 0.400 s
% 18.73/2.80  % (22309)------------------------------
% 18.73/2.80  % (22309)------------------------------
% 19.52/2.83  % (22275)Time limit reached!
% 19.52/2.83  % (22275)------------------------------
% 19.52/2.83  % (22275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.52/2.84  % (22275)Termination reason: Time limit
% 19.52/2.84  
% 19.52/2.84  % (22275)Memory used [KB]: 6652
% 19.52/2.84  % (22275)Time elapsed: 2.418 s
% 19.52/2.84  % (22275)------------------------------
% 19.52/2.84  % (22275)------------------------------
% 20.85/2.98  % (22310)Time limit reached!
% 20.85/2.98  % (22310)------------------------------
% 20.85/2.98  % (22310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.85/3.00  % (22310)Termination reason: Time limit
% 20.85/3.00  % (22310)Termination phase: Saturation
% 20.85/3.00  
% 20.85/3.00  % (22310)Memory used [KB]: 7931
% 20.85/3.00  % (22310)Time elapsed: 0.400 s
% 20.85/3.00  % (22310)------------------------------
% 20.85/3.00  % (22310)------------------------------
% 24.95/3.50  % (22271)Time limit reached!
% 24.95/3.50  % (22271)------------------------------
% 24.95/3.50  % (22271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.95/3.52  % (22271)Termination reason: Time limit
% 24.95/3.52  % (22271)Termination phase: Saturation
% 24.95/3.52  
% 24.95/3.52  % (22271)Memory used [KB]: 29295
% 24.95/3.52  % (22271)Time elapsed: 3.100 s
% 24.95/3.52  % (22271)------------------------------
% 24.95/3.52  % (22271)------------------------------
% 24.95/3.54  % (22268)Time limit reached!
% 24.95/3.54  % (22268)------------------------------
% 24.95/3.54  % (22268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.95/3.54  % (22268)Termination reason: Time limit
% 24.95/3.54  
% 24.95/3.54  % (22268)Memory used [KB]: 26225
% 24.95/3.54  % (22268)Time elapsed: 3.114 s
% 24.95/3.54  % (22268)------------------------------
% 24.95/3.54  % (22268)------------------------------
% 26.76/3.74  % (22279)Time limit reached!
% 26.76/3.74  % (22279)------------------------------
% 26.76/3.74  % (22279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.76/3.74  % (22279)Termination reason: Time limit
% 26.76/3.74  % (22279)Termination phase: Saturation
% 26.76/3.74  
% 26.76/3.74  % (22279)Memory used [KB]: 21748
% 26.76/3.74  % (22279)Time elapsed: 3.300 s
% 26.76/3.74  % (22279)------------------------------
% 26.76/3.74  % (22279)------------------------------
% 29.03/4.03  % (22298)Time limit reached!
% 29.03/4.03  % (22298)------------------------------
% 29.03/4.03  % (22298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.22/4.05  % (22298)Termination reason: Time limit
% 29.22/4.05  
% 29.22/4.05  % (22298)Memory used [KB]: 14583
% 29.22/4.05  % (22298)Time elapsed: 3.007 s
% 29.22/4.05  % (22298)------------------------------
% 29.22/4.05  % (22298)------------------------------
% 30.50/4.23  % (22293)Time limit reached!
% 30.50/4.23  % (22293)------------------------------
% 30.50/4.23  % (22293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.50/4.24  % (22293)Termination reason: Time limit
% 30.50/4.24  % (22293)Termination phase: Saturation
% 30.50/4.24  
% 30.50/4.24  % (22293)Memory used [KB]: 38123
% 30.50/4.24  % (22293)Time elapsed: 3.400 s
% 30.50/4.24  % (22293)------------------------------
% 30.50/4.24  % (22293)------------------------------
% 31.43/4.31  % (22297)Time limit reached!
% 31.43/4.31  % (22297)------------------------------
% 31.43/4.31  % (22297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.43/4.31  % (22297)Termination reason: Time limit
% 31.43/4.31  % (22297)Termination phase: Saturation
% 31.43/4.31  
% 31.43/4.31  % (22297)Memory used [KB]: 16630
% 31.43/4.31  % (22297)Time elapsed: 3.300 s
% 31.43/4.31  % (22297)------------------------------
% 31.43/4.31  % (22297)------------------------------
% 38.77/5.24  % (22277)Time limit reached!
% 38.77/5.24  % (22277)------------------------------
% 38.77/5.24  % (22277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.77/5.24  % (22277)Termination reason: Time limit
% 38.77/5.24  
% 38.77/5.24  % (22277)Memory used [KB]: 27504
% 38.77/5.24  % (22277)Time elapsed: 4.819 s
% 38.77/5.24  % (22277)------------------------------
% 38.77/5.24  % (22277)------------------------------
% 51.22/6.86  % (22295)Refutation found. Thanks to Tanya!
% 51.22/6.86  % SZS status Theorem for theBenchmark
% 51.22/6.86  % SZS output start Proof for theBenchmark
% 51.22/6.86  fof(f70138,plain,(
% 51.22/6.86    $false),
% 51.22/6.86    inference(subsumption_resolution,[],[f70080,f46])).
% 51.22/6.86  fof(f46,plain,(
% 51.22/6.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.22/6.86    inference(equality_resolution,[],[f35])).
% 51.22/6.86  fof(f35,plain,(
% 51.22/6.86    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.22/6.86    inference(cnf_transformation,[],[f1])).
% 51.22/6.86  fof(f1,axiom,(
% 51.22/6.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 51.22/6.86  fof(f70080,plain,(
% 51.22/6.86    ~r1_tarski(sK1,sK1)),
% 51.22/6.86    inference(resolution,[],[f69256,f46])).
% 51.22/6.86  fof(f69256,plain,(
% 51.22/6.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(X0,sK1)) )),
% 51.22/6.86    inference(superposition,[],[f69204,f38])).
% 51.22/6.86  fof(f38,plain,(
% 51.22/6.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 51.22/6.86    inference(cnf_transformation,[],[f22])).
% 51.22/6.86  fof(f22,plain,(
% 51.22/6.86    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.22/6.86    inference(ennf_transformation,[],[f3])).
% 51.22/6.86  fof(f3,axiom,(
% 51.22/6.86    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 51.22/6.86  fof(f69204,plain,(
% 51.22/6.86    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK1)) )),
% 51.22/6.86    inference(subsumption_resolution,[],[f69000,f31717])).
% 51.22/6.86  fof(f31717,plain,(
% 51.22/6.86    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X0),X1)) )),
% 51.22/6.86    inference(resolution,[],[f31526,f43])).
% 51.22/6.86  fof(f43,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 51.22/6.86    inference(definition_unfolding,[],[f34,f41])).
% 51.22/6.86  fof(f41,plain,(
% 51.22/6.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 51.22/6.86    inference(cnf_transformation,[],[f8])).
% 51.22/6.86  fof(f8,axiom,(
% 51.22/6.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 51.22/6.86  fof(f34,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 51.22/6.86    inference(cnf_transformation,[],[f21])).
% 51.22/6.86  fof(f21,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.22/6.86    inference(ennf_transformation,[],[f6])).
% 51.22/6.86  fof(f6,axiom,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 51.22/6.86  fof(f31526,plain,(
% 51.22/6.86    ( ! [X83,X82] : (r1_tarski(X82,k2_xboole_0(X82,X83))) )),
% 51.22/6.86    inference(forward_demodulation,[],[f29292,f29428])).
% 51.22/6.86  fof(f29428,plain,(
% 51.22/6.86    ( ! [X6] : (k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))) = X6) )),
% 51.22/6.86    inference(subsumption_resolution,[],[f29245,f44])).
% 51.22/6.86  fof(f44,plain,(
% 51.22/6.86    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 51.22/6.86    inference(definition_unfolding,[],[f39,f41])).
% 51.22/6.86  fof(f39,plain,(
% 51.22/6.86    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.22/6.86    inference(cnf_transformation,[],[f5])).
% 51.22/6.86  fof(f5,axiom,(
% 51.22/6.86    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 51.22/6.86  fof(f29245,plain,(
% 51.22/6.86    ( ! [X6] : (~r1_tarski(k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))),X6) | k6_subset_1(X6,k6_subset_1(sK0,k2_relat_1(sK2))) = X6) )),
% 51.22/6.86    inference(resolution,[],[f29181,f37])).
% 51.22/6.86  fof(f37,plain,(
% 51.22/6.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 51.22/6.86    inference(cnf_transformation,[],[f1])).
% 51.22/6.86  fof(f29181,plain,(
% 51.22/6.86    ( ! [X74] : (r1_tarski(X74,k6_subset_1(X74,k6_subset_1(sK0,k2_relat_1(sK2))))) )),
% 51.22/6.86    inference(resolution,[],[f534,f46])).
% 51.22/6.86  fof(f534,plain,(
% 51.22/6.86    ( ! [X4,X3] : (~r1_tarski(k6_subset_1(X4,k6_subset_1(sK0,k2_relat_1(sK2))),X3) | r1_tarski(X4,X3)) )),
% 51.22/6.86    inference(superposition,[],[f42,f244])).
% 51.22/6.86  fof(f244,plain,(
% 51.22/6.86    ( ! [X2] : (k2_xboole_0(k6_subset_1(sK0,k2_relat_1(sK2)),X2) = X2) )),
% 51.22/6.86    inference(resolution,[],[f170,f38])).
% 51.22/6.86  fof(f170,plain,(
% 51.22/6.86    ( ! [X3] : (r1_tarski(k6_subset_1(sK0,k2_relat_1(sK2)),X3)) )),
% 51.22/6.86    inference(resolution,[],[f161,f43])).
% 51.22/6.86  fof(f161,plain,(
% 51.22/6.86    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0))) )),
% 51.22/6.86    inference(resolution,[],[f96,f46])).
% 51.22/6.86  fof(f96,plain,(
% 51.22/6.86    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X1),X0) | r1_tarski(sK0,X0)) )),
% 51.22/6.86    inference(resolution,[],[f60,f33])).
% 51.22/6.86  fof(f33,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 51.22/6.86    inference(cnf_transformation,[],[f20])).
% 51.22/6.86  fof(f20,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 51.22/6.86    inference(ennf_transformation,[],[f2])).
% 51.22/6.86  fof(f2,axiom,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 51.22/6.86  fof(f60,plain,(
% 51.22/6.86    ( ! [X1] : (~r1_tarski(k2_relat_1(sK2),X1) | r1_tarski(sK0,X1)) )),
% 51.22/6.86    inference(resolution,[],[f28,f31])).
% 51.22/6.86  fof(f31,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 51.22/6.86    inference(cnf_transformation,[],[f18])).
% 51.22/6.86  fof(f18,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 51.22/6.86    inference(flattening,[],[f17])).
% 51.22/6.86  fof(f17,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 51.22/6.86    inference(ennf_transformation,[],[f4])).
% 51.22/6.86  fof(f4,axiom,(
% 51.22/6.86    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 51.22/6.86  fof(f28,plain,(
% 51.22/6.86    r1_tarski(sK0,k2_relat_1(sK2))),
% 51.22/6.86    inference(cnf_transformation,[],[f14])).
% 51.22/6.86  fof(f14,plain,(
% 51.22/6.86    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 51.22/6.86    inference(flattening,[],[f13])).
% 51.22/6.86  fof(f13,plain,(
% 51.22/6.86    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 51.22/6.86    inference(ennf_transformation,[],[f12])).
% 51.22/6.86  fof(f12,negated_conjecture,(
% 51.22/6.86    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 51.22/6.86    inference(negated_conjecture,[],[f11])).
% 51.22/6.86  fof(f11,conjecture,(
% 51.22/6.86    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 51.22/6.86  fof(f42,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.22/6.86    inference(definition_unfolding,[],[f32,f41])).
% 51.22/6.86  fof(f32,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.22/6.86    inference(cnf_transformation,[],[f19])).
% 51.22/6.86  fof(f19,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.22/6.86    inference(ennf_transformation,[],[f7])).
% 51.22/6.86  fof(f7,axiom,(
% 51.22/6.86    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.22/6.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 51.22/6.86  fof(f29292,plain,(
% 51.22/6.86    ( ! [X83,X82] : (r1_tarski(X82,k6_subset_1(k2_xboole_0(X82,X83),k6_subset_1(sK0,k2_relat_1(sK2))))) )),
% 51.22/6.86    inference(resolution,[],[f29181,f33])).
% 51.22/6.86  fof(f69000,plain,(
% 51.22/6.86    ( ! [X0] : (~r1_tarski(k6_subset_1(sK0,sK0),X0) | ~r1_tarski(k2_xboole_0(sK1,X0),sK1)) )),
% 51.22/6.86    inference(superposition,[],[f74,f68859])).
% 51.22/6.86  fof(f68859,plain,(
% 51.22/6.86    k6_subset_1(sK0,sK1) = k6_subset_1(sK0,sK0)),
% 51.22/6.86    inference(backward_demodulation,[],[f64682,f65443])).
% 51.22/6.86  fof(f65443,plain,(
% 51.22/6.86    ( ! [X216] : (k6_subset_1(sK0,sK0) = k9_relat_1(sK2,k6_subset_1(X216,X216))) )),
% 51.22/6.86    inference(superposition,[],[f378,f58053])).
% 51.22/6.86  fof(f58053,plain,(
% 51.22/6.86    ( ! [X128,X129] : (k10_relat_1(sK2,k6_subset_1(X129,X129)) = k6_subset_1(X128,X128)) )),
% 51.22/6.86    inference(resolution,[],[f32070,f4029])).
% 51.22/6.86  fof(f4029,plain,(
% 51.22/6.86    ( ! [X23,X22] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(X22,X22)),X23)) )),
% 51.22/6.86    inference(resolution,[],[f511,f46])).
% 51.22/6.86  fof(f511,plain,(
% 51.22/6.86    ( ! [X6,X8,X7,X5] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,X5),X8),k2_xboole_0(k10_relat_1(sK2,X6),X7)) | r1_tarski(k10_relat_1(sK2,k6_subset_1(X5,X6)),X7)) )),
% 51.22/6.86    inference(resolution,[],[f132,f33])).
% 51.22/6.86  fof(f132,plain,(
% 51.22/6.86    ( ! [X6,X4,X5] : (~r1_tarski(k10_relat_1(sK2,X4),k2_xboole_0(k10_relat_1(sK2,X5),X6)) | r1_tarski(k10_relat_1(sK2,k6_subset_1(X4,X5)),X6)) )),
% 51.22/6.86    inference(superposition,[],[f43,f51])).
% 51.22/6.86  fof(f51,plain,(
% 51.22/6.86    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 51.22/6.86    inference(subsumption_resolution,[],[f49,f25])).
% 51.22/6.86  fof(f25,plain,(
% 51.22/6.86    v1_relat_1(sK2)),
% 51.22/6.86    inference(cnf_transformation,[],[f14])).
% 51.22/6.86  fof(f49,plain,(
% 51.22/6.86    ( ! [X0,X1] : (~v1_relat_1(sK2) | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 51.22/6.86    inference(resolution,[],[f26,f40])).
% 51.22/6.86  fof(f40,plain,(
% 51.22/6.86    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 51.22/6.86    inference(cnf_transformation,[],[f24])).
% 51.22/6.86  fof(f24,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 51.22/6.86    inference(flattening,[],[f23])).
% 51.22/6.86  fof(f23,plain,(
% 51.22/6.86    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 51.22/6.86    inference(ennf_transformation,[],[f9])).
% 52.00/6.88  fof(f9,axiom,(
% 52.00/6.88    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 52.00/6.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 52.00/6.88  fof(f26,plain,(
% 52.00/6.88    v1_funct_1(sK2)),
% 52.00/6.88    inference(cnf_transformation,[],[f14])).
% 52.00/6.88  fof(f32070,plain,(
% 52.00/6.88    ( ! [X163,X164] : (~r1_tarski(X163,k6_subset_1(X164,X164)) | k6_subset_1(X164,X164) = X163) )),
% 52.00/6.88    inference(resolution,[],[f31717,f37])).
% 52.00/6.88  fof(f378,plain,(
% 52.00/6.88    ( ! [X2] : (k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2)))) )),
% 52.00/6.88    inference(subsumption_resolution,[],[f377,f26])).
% 52.00/6.88  fof(f377,plain,(
% 52.00/6.88    ( ! [X2] : (~v1_funct_1(sK2) | k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2)))) )),
% 52.00/6.88    inference(subsumption_resolution,[],[f371,f25])).
% 52.00/6.88  fof(f371,plain,(
% 52.00/6.88    ( ! [X2] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k6_subset_1(sK0,X2) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X2)))) )),
% 52.00/6.88    inference(resolution,[],[f350,f30])).
% 52.00/6.88  fof(f30,plain,(
% 52.00/6.88    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 52.00/6.88    inference(cnf_transformation,[],[f16])).
% 52.00/6.88  fof(f16,plain,(
% 52.00/6.88    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 52.00/6.88    inference(flattening,[],[f15])).
% 52.00/6.88  fof(f15,plain,(
% 52.00/6.88    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 52.00/6.88    inference(ennf_transformation,[],[f10])).
% 52.00/6.88  fof(f10,axiom,(
% 52.00/6.88    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 52.00/6.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 52.00/6.88  fof(f350,plain,(
% 52.00/6.88    ( ! [X3] : (r1_tarski(k6_subset_1(sK0,X3),k2_relat_1(sK2))) )),
% 52.00/6.88    inference(resolution,[],[f336,f43])).
% 52.00/6.88  fof(f336,plain,(
% 52.00/6.88    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(X2,k2_relat_1(sK2)))) )),
% 52.00/6.88    inference(resolution,[],[f98,f44])).
% 52.00/6.88  fof(f98,plain,(
% 52.00/6.88    ( ! [X4,X5] : (~r1_tarski(k6_subset_1(k2_relat_1(sK2),X4),X5) | r1_tarski(sK0,k2_xboole_0(X4,X5))) )),
% 52.00/6.88    inference(resolution,[],[f60,f42])).
% 52.00/6.88  fof(f64682,plain,(
% 52.00/6.88    ( ! [X26] : (k6_subset_1(sK0,sK1) = k9_relat_1(sK2,k6_subset_1(X26,X26))) )),
% 52.00/6.88    inference(superposition,[],[f378,f58048])).
% 52.00/6.88  fof(f58048,plain,(
% 52.00/6.88    ( ! [X121] : (k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k6_subset_1(X121,X121)) )),
% 52.00/6.88    inference(resolution,[],[f32070,f650])).
% 52.00/6.88  fof(f650,plain,(
% 52.00/6.88    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X0)) )),
% 52.00/6.88    inference(resolution,[],[f402,f132])).
% 52.00/6.88  fof(f402,plain,(
% 52.00/6.88    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))) )),
% 52.00/6.88    inference(resolution,[],[f118,f46])).
% 52.00/6.88  fof(f118,plain,(
% 52.00/6.88    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X1),X0) | r1_tarski(k10_relat_1(sK2,sK0),X0)) )),
% 52.00/6.88    inference(resolution,[],[f67,f33])).
% 52.00/6.88  fof(f67,plain,(
% 52.00/6.88    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,sK1),X1) | r1_tarski(k10_relat_1(sK2,sK0),X1)) )),
% 52.00/6.88    inference(resolution,[],[f27,f31])).
% 52.00/6.88  fof(f27,plain,(
% 52.00/6.88    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 52.00/6.88    inference(cnf_transformation,[],[f14])).
% 52.00/6.88  fof(f74,plain,(
% 52.00/6.88    ( ! [X4,X5] : (~r1_tarski(k6_subset_1(sK0,X4),X5) | ~r1_tarski(k2_xboole_0(X4,X5),sK1)) )),
% 52.00/6.88    inference(resolution,[],[f54,f42])).
% 52.00/6.88  fof(f54,plain,(
% 52.00/6.88    ( ! [X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(X1,sK1)) )),
% 52.00/6.88    inference(resolution,[],[f29,f31])).
% 52.00/6.88  fof(f29,plain,(
% 52.00/6.88    ~r1_tarski(sK0,sK1)),
% 52.00/6.88    inference(cnf_transformation,[],[f14])).
% 52.00/6.88  % SZS output end Proof for theBenchmark
% 52.00/6.88  % (22295)------------------------------
% 52.00/6.88  % (22295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.00/6.88  % (22295)Termination reason: Refutation
% 52.00/6.88  
% 52.00/6.88  % (22295)Memory used [KB]: 38890
% 52.00/6.88  % (22295)Time elapsed: 5.937 s
% 52.00/6.88  % (22295)------------------------------
% 52.00/6.88  % (22295)------------------------------
% 52.00/6.89  % (22259)Success in time 6.513 s
%------------------------------------------------------------------------------

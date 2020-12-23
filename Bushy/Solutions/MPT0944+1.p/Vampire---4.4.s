%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t9_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  65 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(k1_wellord2(X1))
          & r1_tarski(X1,X0) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( r1_tarski(X1,X0)
           => v2_wellord1(k1_wellord2(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( r1_tarski(X1,X0)
         => v2_wellord1(k1_wellord2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t9_wellord2.p',t9_wellord2)).

fof(f46,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t9_wellord2.p',t7_wellord2)).

fof(f45,plain,(
    ~ v2_wellord1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t9_wellord2.p',dt_k1_wellord2)).

fof(f44,plain,
    ( ~ v2_wellord1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f26,plain,(
    ~ v2_wellord1(k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ v2_wellord1(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f36,f25])).

fof(f25,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t9_wellord2.p',t8_wellord2)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t9_wellord2.p',t32_wellord1)).
%------------------------------------------------------------------------------

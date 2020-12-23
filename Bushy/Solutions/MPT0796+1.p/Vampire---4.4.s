%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t48_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  29 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ~ r4_wellord1(X0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r4_wellord1(X0,X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r4_wellord1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t48_wellord1.p',t48_wellord1)).

fof(f36,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t48_wellord1.p',dt_k6_relat_1)).

fof(f35,plain,
    ( ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f21,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t48_wellord1.p',fc3_funct_1)).

fof(f32,plain,
    ( ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t48_wellord1.p',t47_wellord1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK0,sK0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r3_wellord1(sK0,sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r3_wellord1(sK0,sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,(
    ~ r4_wellord1(sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t48_wellord1.p',d8_wellord1)).
%------------------------------------------------------------------------------

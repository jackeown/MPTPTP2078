%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t14_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   14 (  22 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  55 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f12])).

fof(f12,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k2_xboole_0(X0,X1))
      & v1_finset_1(X1)
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X0) )
       => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t14_finset_1.p',t14_finset_1)).

fof(f23,plain,(
    ~ v1_finset_1(sK0) ),
    inference(subsumption_resolution,[],[f18,f13])).

fof(f13,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    ~ v1_finset_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_xboole_0(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t14_finset_1.p',fc9_finset_1)).
%------------------------------------------------------------------------------

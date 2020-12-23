%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t185_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  37 expanded)
%              Number of leaves         :    2 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 ( 123 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f15,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
               => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
             => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t185_relat_1.p',t185_relat_1)).

fof(f51,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) = k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f48,f27])).

fof(f27,plain,(
    ! [X2,X3] : k7_relat_1(sK0,k2_xboole_0(X2,X3)) = k2_xboole_0(k7_relat_1(sK0,X2),k7_relat_1(sK0,X3)) ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t185_relat_1.p',t107_relat_1)).

fof(f48,plain,(
    k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK0,sK3)) ),
    inference(superposition,[],[f31,f14])).

fof(f14,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] : k7_relat_1(sK1,k2_xboole_0(sK2,X0)) = k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X0)) ),
    inference(superposition,[],[f26,f13])).

fof(f13,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] : k7_relat_1(sK1,k2_xboole_0(X0,X1)) = k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------

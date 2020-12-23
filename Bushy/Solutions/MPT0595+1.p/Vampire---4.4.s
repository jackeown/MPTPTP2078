%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t199_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:57 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  43 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 ( 153 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f14,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) != k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) != k2_relat_1(k5_relat_1(X1,X2))
              & k2_relat_1(X0) = k2_relat_1(X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( k2_relat_1(X0) = k2_relat_1(X1)
                 => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t199_relat_1.p',t199_relat_1)).

fof(f54,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f53,f32])).

fof(f32,plain,(
    k2_relat_1(k5_relat_1(sK0,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(resolution,[],[f20,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k5_relat_1(sK0,X3)) = k9_relat_1(X3,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t199_relat_1.p',t160_relat_1)).

fof(f53,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f51,f13])).

fof(f13,plain,(
    k2_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    k2_relat_1(k5_relat_1(sK1,sK2)) = k9_relat_1(sK2,k2_relat_1(sK1)) ),
    inference(resolution,[],[f26,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k5_relat_1(X5,sK2)) = k9_relat_1(sK2,k2_relat_1(X5)) ) ),
    inference(resolution,[],[f17,f12])).
%------------------------------------------------------------------------------

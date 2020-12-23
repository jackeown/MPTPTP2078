%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 (1416 expanded)
%              Number of leaves         :    6 ( 243 expanded)
%              Depth                    :   18
%              Number of atoms          :  269 (9418 expanded)
%              Number of equality atoms :   98 (3528 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f329,f67])).

fof(f67,plain,(
    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f27,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
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
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f66,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f65,f23])).

fof(f23,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f64,f23])).

fof(f64,plain,
    ( sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,
    ( ~ v1_relat_1(sK2)
    | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f21,f46])).

fof(f46,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f329,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f315,f324])).

fof(f324,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f300,f157])).

fof(f157,plain,(
    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) ),
    inference(forward_demodulation,[],[f148,f136])).

fof(f136,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f130,f132])).

fof(f132,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f62,plain,
    ( sK2 = k6_relat_1(sK0)
    | r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f61,f23])).

fof(f61,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f60,f23])).

fof(f60,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f52,f20])).

fof(f52,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f21,f47])).

fof(f47,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f93,f22])).

fof(f22,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f92,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f91,f21])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f90,f20])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(superposition,[],[f38,f26])).

fof(f26,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f130,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) ),
    inference(resolution,[],[f94,f107])).

fof(f107,plain,(
    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) ),
    inference(resolution,[],[f103,f63])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(k1_funct_1(sK2,X1),sK0) ) ),
    inference(forward_demodulation,[],[f102,f23])).

fof(f102,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f101,f20])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X1),sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f99,f21])).

fof(f99,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X1),sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f31,f88])).

fof(f88,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f87,f20])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f24,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(f148,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) ),
    inference(resolution,[],[f113,f94])).

fof(f113,plain,(
    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))),sK0) ),
    inference(resolution,[],[f107,f103])).

fof(f300,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))
    | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) ),
    inference(resolution,[],[f162,f149])).

fof(f149,plain,(
    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),sK0) ),
    inference(resolution,[],[f113,f103])).

fof(f162,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X4)
      | sK3(sK0,sK2) = X4 ) ),
    inference(resolution,[],[f83,f63])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f25,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f81,f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f80,f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f39,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f315,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) ),
    inference(subsumption_resolution,[],[f298,f230])).

fof(f230,plain,(
    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))) ),
    inference(forward_demodulation,[],[f220,f157])).

fof(f220,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))) ),
    inference(resolution,[],[f149,f94])).

fof(f298,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))))
    | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) ),
    inference(resolution,[],[f162,f221])).

fof(f221,plain,(
    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),sK0) ),
    inference(resolution,[],[f149,f103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31860)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (31855)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (31856)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31862)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (31876)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (31880)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (31858)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (31866)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (31878)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (31860)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (31865)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (31871)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (31870)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (31869)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (31864)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (31862)Refutation not found, incomplete strategy% (31862)------------------------------
% 0.21/0.52  % (31862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31862)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31862)Memory used [KB]: 1663
% 0.21/0.52  % (31862)Time elapsed: 0.103 s
% 0.21/0.52  % (31862)------------------------------
% 0.21/0.52  % (31862)------------------------------
% 0.21/0.52  % (31877)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (31859)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f329,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    sK2 != k6_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK2 = k6_relat_1(sK0) | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f65,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f64,f23])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f21,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f315,f324])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f300,f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))),
% 0.21/0.52    inference(forward_demodulation,[],[f148,f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f130,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.52    inference(resolution,[],[f94,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f62,f27])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK2 = k6_relat_1(sK0) | r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f23])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    r2_hidden(sK3(sK0,sK2),sK0) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f60,f23])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f20])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f21,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f93,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f21])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f20])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(superposition,[],[f38,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),
% 0.21/0.52    inference(resolution,[],[f94,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)),
% 0.21/0.52    inference(resolution,[],[f103,f63])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK2,X1),sK0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f102,f23])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X1),sK0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f101,f20])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X1),sK0) | ~v1_relat_1(sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f21])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X1),sK0) | ~v1_relat_1(sK2)) )),
% 0.21/0.52    inference(superposition,[],[f31,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f87,f20])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f24,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,k6_relat_1(X1)))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))),
% 0.21/0.52    inference(resolution,[],[f113,f94])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))),sK0)),
% 0.21/0.52    inference(resolution,[],[f107,f103])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),
% 0.21/0.52    inference(resolution,[],[f162,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),sK0)),
% 0.21/0.52    inference(resolution,[],[f113,f103])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X4) | sK3(sK0,sK2) = X4) )),
% 0.21/0.52    inference(resolution,[],[f83,f63])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f82,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v2_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f28])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f29])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f39,f22])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f298,f230])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3(sK0,sK2)) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))))),
% 0.21/0.52    inference(forward_demodulation,[],[f220,f157])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))))),
% 0.21/0.52    inference(resolution,[],[f149,f94])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))) | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))),
% 0.21/0.52    inference(resolution,[],[f162,f221])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),sK0)),
% 0.21/0.52    inference(resolution,[],[f149,f103])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31860)------------------------------
% 0.21/0.52  % (31860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31860)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31860)Memory used [KB]: 6268
% 0.21/0.52  % (31860)Time elapsed: 0.101 s
% 0.21/0.52  % (31860)------------------------------
% 0.21/0.52  % (31860)------------------------------
% 0.21/0.52  % (31854)Success in time 0.164 s
%------------------------------------------------------------------------------

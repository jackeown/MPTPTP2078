%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (1196 expanded)
%              Number of leaves         :    5 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  279 (8438 expanded)
%              Number of equality atoms :   95 (3357 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f494,plain,(
    $false ),
    inference(subsumption_resolution,[],[f492,f63])).

fof(f63,plain,(
    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f62,f24])).

fof(f24,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
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
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

fof(f62,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f61,f21])).

fof(f21,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f60,f21])).

fof(f60,plain,
    ( sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,
    ( ~ v1_relat_1(sK2)
    | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f19,f42])).

fof(f42,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f492,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f473,f484])).

fof(f484,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f462,f135])).

fof(f135,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f126,f129])).

fof(f129,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(resolution,[],[f96,f59])).

fof(f59,plain,(
    r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( sK2 = k6_relat_1(sK0)
    | r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f57,f21])).

fof(f57,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f56,f21])).

fof(f56,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f48,f18])).

fof(f48,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2))
    | sK2 = k6_relat_1(k1_relat_1(sK2)) ),
    inference(resolution,[],[f19,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f95,f20])).

fof(f20,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f94,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f92,f18])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f26,plain,(
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
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f126,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) ),
    inference(resolution,[],[f96,f112])).

fof(f112,plain,(
    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) ),
    inference(resolution,[],[f108,f59])).

fof(f108,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r2_hidden(k1_funct_1(sK2,X2),sK0) ) ),
    inference(forward_demodulation,[],[f107,f20])).

fof(f107,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f106,f20])).

fof(f106,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f105,f25])).

fof(f105,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f104,f19])).

fof(f104,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f103,f18])).

fof(f103,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f32,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f462,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) != k1_funct_1(sK1,sK3(sK0,sK2))
    | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))) ),
    inference(resolution,[],[f148,f115])).

fof(f115,plain,(
    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))),sK0) ),
    inference(resolution,[],[f112,f108])).

fof(f148,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK0)
      | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X6)
      | sK3(sK0,sK2) = X6 ) ),
    inference(resolution,[],[f80,f59])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f78,f25])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f35,f20])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f473,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f459,f134])).

fof(f134,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f133,f129])).

fof(f133,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) ),
    inference(backward_demodulation,[],[f125,f126])).

fof(f125,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) ),
    inference(resolution,[],[f96,f115])).

fof(f459,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) != k1_funct_1(sK1,sK3(sK0,sK2))
    | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) ),
    inference(resolution,[],[f148,f123])).

fof(f123,plain,(
    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),sK0) ),
    inference(resolution,[],[f115,f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (31878)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.47  % (31894)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (31874)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (31887)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (31869)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (31871)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (31890)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (31870)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31876)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (31872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (31876)Refutation not found, incomplete strategy% (31876)------------------------------
% 0.21/0.51  % (31876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31876)Memory used [KB]: 1663
% 0.21/0.51  % (31876)Time elapsed: 0.101 s
% 0.21/0.51  % (31876)------------------------------
% 0.21/0.51  % (31876)------------------------------
% 0.21/0.51  % (31879)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (31877)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (31892)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (31884)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (31873)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (31880)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (31885)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (31874)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f492,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f62,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    sK2 != k6_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK2 = k6_relat_1(sK0) | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f60,f21])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f19,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f492,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f473,f484])).
% 0.21/0.52  fof(f484,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f462,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f126,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.52    inference(resolution,[],[f96,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f24])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    sK2 = k6_relat_1(sK0) | r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f57,f21])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    r2_hidden(sK3(sK0,sK2),sK0) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f56,f21])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(subsumption_resolution,[],[f48,f18])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f19,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f95,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f94,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f19])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f92,f18])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK1,k1_funct_1(sK2,X0))) )),
% 0.21/0.52    inference(superposition,[],[f34,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))),
% 0.21/0.52    inference(resolution,[],[f96,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)),
% 0.21/0.52    inference(resolution,[],[f108,f59])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(k1_funct_1(sK2,X2),sK0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f107,f20])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f106,f20])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f105,f25])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f19])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f103,f18])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f91,f26])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X2),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f32,f23])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) != k1_funct_1(sK1,sK3(sK0,sK2)) | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),
% 0.21/0.52    inference(resolution,[],[f148,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))),sK0)),
% 0.21/0.52    inference(resolution,[],[f112,f108])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,sK0) | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X6) | sK3(sK0,sK2) = X6) )),
% 0.21/0.52    inference(resolution,[],[f80,f59])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v2_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f25])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f76,f26])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f35,f20])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.52  fof(f473,plain,(
% 0.21/0.52    sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f459,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.52    inference(backward_demodulation,[],[f133,f129])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) = k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2)))),
% 0.21/0.52    inference(backward_demodulation,[],[f125,f126])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))) = k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))))),
% 0.21/0.52    inference(resolution,[],[f96,f115])).
% 0.21/0.52  fof(f459,plain,(
% 0.21/0.52    k1_funct_1(sK1,k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))) != k1_funct_1(sK1,sK3(sK0,sK2)) | sK3(sK0,sK2) = k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2))))),
% 0.21/0.52    inference(resolution,[],[f148,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK2,k1_funct_1(sK2,k1_funct_1(sK2,sK3(sK0,sK2)))),sK0)),
% 0.21/0.52    inference(resolution,[],[f115,f108])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31874)------------------------------
% 0.21/0.52  % (31874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31874)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31874)Memory used [KB]: 6396
% 0.21/0.52  % (31874)Time elapsed: 0.131 s
% 0.21/0.52  % (31874)------------------------------
% 0.21/0.52  % (31874)------------------------------
% 0.21/0.52  % (31891)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (31868)Success in time 0.164 s
%------------------------------------------------------------------------------

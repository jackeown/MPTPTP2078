%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 297 expanded)
%              Number of leaves         :    5 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  267 (2079 expanded)
%              Number of equality atoms :   86 ( 861 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(subsumption_resolution,[],[f546,f378])).

fof(f378,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) != k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f370,f63])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f370,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) != k1_funct_1(sK1,sK3(sK0,sK2))
    | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(resolution,[],[f132,f112])).

fof(f112,plain,(
    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) ),
    inference(resolution,[],[f108,f59])).

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

fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(k1_funct_1(sK2,X1),sK0) ) ),
    inference(forward_demodulation,[],[f107,f20])).

fof(f20,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f106,f20])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f105,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f104,f19])).

fof(f104,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f103,f18])).

fof(f103,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f32,f23])).

fof(f23,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f132,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X5)
      | sK3(sK0,sK2) = X5 ) ),
    inference(resolution,[],[f81,f59])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f79,f25])).

fof(f79,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f546,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f545,f23])).

fof(f545,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f541,f25])).

fof(f541,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2)) ),
    inference(resolution,[],[f177,f26])).

fof(f177,plain,(
    ! [X8] :
      ( ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | k1_funct_1(k5_relat_1(sK2,X8),sK3(sK0,sK2)) = k1_funct_1(X8,k1_funct_1(sK2,sK3(sK0,sK2))) ) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f91,f18])).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) ) ),
    inference(subsumption_resolution,[],[f87,f19])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2)) ) ),
    inference(superposition,[],[f34,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
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
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:37:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (29281)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29273)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (29271)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (29275)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (29274)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (29293)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (29272)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (29284)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (29279)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (29283)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (29275)Refutation not found, incomplete strategy% (29275)------------------------------
% 0.21/0.52  % (29275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29290)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (29287)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (29292)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (29276)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (29291)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (29275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29275)Memory used [KB]: 1663
% 0.21/0.52  % (29275)Time elapsed: 0.097 s
% 0.21/0.52  % (29275)------------------------------
% 0.21/0.52  % (29275)------------------------------
% 0.21/0.53  % (29282)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (29280)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (29273)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f547,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f546,f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) != k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f370,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f62,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    sK2 != k6_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    sK2 = k6_relat_1(sK0) | sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f61,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f60,f21])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f49,f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | sK3(k1_relat_1(sK2),sK2) != k1_funct_1(sK2,sK3(k1_relat_1(sK2),sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f19,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) != k1_funct_1(sK1,sK3(sK0,sK2)) | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f132,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)),
% 0.21/0.53    inference(resolution,[],[f108,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f58,f24])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    sK2 = k6_relat_1(sK0) | r2_hidden(sK3(sK0,sK2),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f57,f21])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    r2_hidden(sK3(sK0,sK2),sK0) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f56,f21])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f48,f18])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | r2_hidden(sK3(k1_relat_1(sK2),sK2),k1_relat_1(sK2)) | sK2 = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f19,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.53    inference(equality_resolution,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK2,X1),sK0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f107,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,sK0) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f20])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f104,f19])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f18])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    v1_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK2,X1),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f32,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    sK1 = k5_relat_1(sK2,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X5] : (~r2_hidden(X5,sK0) | k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,X5) | sK3(sK0,sK2) = X5) )),
% 0.21/0.53    inference(resolution,[],[f81,f59])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    v2_funct_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f79,f25])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f76,f26])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f35,f20])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.53  fof(f546,plain,(
% 0.21/0.53    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f545,f23])).
% 0.21/0.53  fof(f545,plain,(
% 0.21/0.53    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f541,f25])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(k5_relat_1(sK2,sK1),sK3(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f177,f26])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X8] : (~v1_funct_1(X8) | ~v1_relat_1(X8) | k1_funct_1(k5_relat_1(sK2,X8),sK3(sK0,sK2)) = k1_funct_1(X8,k1_funct_1(sK2,sK3(sK0,sK2)))) )),
% 0.21/0.53    inference(resolution,[],[f92,f59])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f18])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f19])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | k1_funct_1(k5_relat_1(sK2,X3),X2) = k1_funct_1(X3,k1_funct_1(sK2,X2))) )),
% 0.21/0.53    inference(superposition,[],[f34,f21])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (29273)------------------------------
% 0.21/0.53  % (29273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29273)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (29273)Memory used [KB]: 6524
% 0.21/0.53  % (29273)Time elapsed: 0.107 s
% 0.21/0.53  % (29273)------------------------------
% 0.21/0.53  % (29273)------------------------------
% 0.21/0.53  % (29269)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (29268)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (29267)Success in time 0.16 s
%------------------------------------------------------------------------------

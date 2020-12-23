%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 253 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  246 (1183 expanded)
%              Number of equality atoms :   76 ( 348 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(subsumption_resolution,[],[f429,f23])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0
        | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0 )
      & r2_hidden(X0,k1_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k1_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
            & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f429,plain,(
    ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f423,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f423,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f417,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f417,plain,(
    ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f416,f396])).

fof(f396,plain,(
    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(trivial_inequality_removal,[],[f388])).

fof(f388,plain,
    ( sK0 != sK0
    | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(backward_demodulation,[],[f21,f387])).

fof(f387,plain,(
    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f386,f23])).

fof(f386,plain,
    ( sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f380,f22])).

fof(f380,plain,
    ( sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f377,f29])).

fof(f377,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f132,f25])).

fof(f25,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f132,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f131,f97])).

fof(f97,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f76,f22])).

fof(f76,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,(
    ! [X7] :
      ( ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ r2_hidden(X7,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f130,f23])).

fof(f130,plain,(
    ! [X7] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ r2_hidden(X7,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7 ) ),
    inference(subsumption_resolution,[],[f108,f22])).

fof(f108,plain,(
    ! [X7] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ r2_hidden(X7,k1_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7 ) ),
    inference(resolution,[],[f24,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | k1_funct_1(X1,X2) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f21,plain,
    ( sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f416,plain,
    ( sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f413,f387])).

fof(f413,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) ),
    inference(resolution,[],[f245,f25])).

fof(f245,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f244,f23])).

fof(f244,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f243,f22])).

fof(f243,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f230,f97])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k2_funct_1(sK1))
      | ~ v1_funct_1(k2_funct_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0) ) ),
    inference(superposition,[],[f42,f223])).

fof(f223,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f222,f52])).

fof(f52,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f222,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    inference(forward_demodulation,[],[f220,f111])).

fof(f111,plain,(
    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f110,f23])).

fof(f110,plain,
    ( ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1)) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f220,plain,(
    k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f53,f97])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:33:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (11511)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (11510)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (11510)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f430,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f429,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) != X0 | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) != X0) & (r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.47  fof(f429,plain,(
% 0.21/0.47    ~v1_funct_1(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f423,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f423,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f417,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.47  fof(f417,plain,(
% 0.21/0.47    ~v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f416,f396])).
% 0.21/0.47  fof(f396,plain,(
% 0.21/0.47    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f388])).
% 0.21/0.47  fof(f388,plain,(
% 0.21/0.47    sK0 != sK0 | sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f21,f387])).
% 0.21/0.47  fof(f387,plain,(
% 0.21/0.47    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f386,f23])).
% 0.21/0.47  fof(f386,plain,(
% 0.21/0.47    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_funct_1(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f380,f22])).
% 0.21/0.47  fof(f380,plain,(
% 0.21/0.47    sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1)),
% 0.21/0.47    inference(resolution,[],[f377,f29])).
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    ~v1_funct_1(k2_funct_1(sK1)) | sK0 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.47    inference(resolution,[],[f132,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f22])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f23,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X7] : (~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(X7,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f23])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X7] : (~v1_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(X7,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f22])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X7] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(X7,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X7)) = X7) )),
% 0.21/0.47    inference(resolution,[],[f24,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X3] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3) )),
% 0.21/0.47    inference(equality_resolution,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.47    inference(equality_resolution,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | k1_funct_1(X1,X2) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k2_relat_1(X0) = k1_relat_1(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v2_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    sK0 != k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | sK0 != k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f416,plain,(
% 0.21/0.47    sK0 = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0) | ~v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(forward_demodulation,[],[f413,f387])).
% 0.21/0.47  fof(f413,plain,(
% 0.21/0.47    ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),sK0)),
% 0.21/0.47    inference(resolution,[],[f245,f25])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f244,f23])).
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f243,f22])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f230,f97])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,k2_funct_1(sK1)),X0)) )),
% 0.21/0.47    inference(superposition,[],[f42,f223])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))),
% 0.21/0.47    inference(forward_demodulation,[],[f222,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f22,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))),
% 0.21/0.47    inference(forward_demodulation,[],[f220,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f23])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ~v1_funct_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f98,f22])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k2_relat_1(sK1) = k1_relat_1(k2_funct_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f24,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    k1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) = k10_relat_1(sK1,k1_relat_1(k2_funct_1(sK1)))),
% 0.21/0.47    inference(resolution,[],[f53,f97])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f22,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11510)------------------------------
% 0.21/0.47  % (11510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11510)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11510)Memory used [KB]: 1791
% 0.21/0.47  % (11510)Time elapsed: 0.016 s
% 0.21/0.47  % (11510)------------------------------
% 0.21/0.47  % (11510)------------------------------
% 0.21/0.48  % (11494)Success in time 0.116 s
%------------------------------------------------------------------------------

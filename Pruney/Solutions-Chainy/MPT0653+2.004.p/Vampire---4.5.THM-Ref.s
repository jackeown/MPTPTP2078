%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 514 expanded)
%              Number of leaves         :    8 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  299 (3913 expanded)
%              Number of equality atoms :  102 (1539 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f217,f164])).

fof(f164,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f41,f90])).

fof(f90,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & ! [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <=> k1_funct_1(X1,X3) = X2 )
              | ~ r2_hidden(X3,k1_relat_1(X1))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k2_relat_1(X0) = k1_relat_1(X1)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2,X3] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X2,k1_relat_1(X0)) )
                   => ( k1_funct_1(X0,X2) = X3
                    <=> k1_funct_1(X1,X3) = X2 ) )
                & k2_relat_1(X0) = k1_relat_1(X1)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k2_relat_1(X0) = k1_relat_1(X1)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f89,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f38,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f217,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f216,f209])).

fof(f209,plain,(
    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f206,f208])).

fof(f208,plain,(
    sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f204,f188])).

fof(f188,plain,(
    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f187,f164])).

fof(f187,plain,
    ( r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f186,f96])).

fof(f96,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f182,f92])).

fof(f92,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f182,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | sK1 = k4_relat_1(sK0) ),
    inference(resolution,[],[f81,f88])).

fof(f88,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f87,f42])).

fof(f87,plain,
    ( ~ v1_relat_1(sK0)
    | v1_funct_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v1_funct_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(sK1,X0),k2_relat_1(sK0))
      | sK1 = X0 ) ),
    inference(forward_demodulation,[],[f80,f40])).

fof(f40,plain,(
    k1_relat_1(sK1) = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k2_relat_1(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1))
      | sK1 = X0 ) ),
    inference(forward_demodulation,[],[f79,f40])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1))
      | sK1 = X0 ) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f37,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f204,plain,
    ( ~ r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))
    | sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))) ),
    inference(resolution,[],[f194,f67])).

fof(f67,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k2_relat_1(sK0))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f66,f40])).

fof(f66,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f63,f39])).

fof(f39,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) != X2
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f194,plain,(
    r2_hidden(k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))),k2_relat_1(sK1)) ),
    inference(resolution,[],[f188,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f144,f36])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK1)
      | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f141,f37])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f206,plain,(
    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))))) ),
    inference(resolution,[],[f194,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,X1)) = X1 ) ),
    inference(forward_demodulation,[],[f121,f90])).

fof(f121,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK0)
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK0)
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1 ) ),
    inference(superposition,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f216,plain,
    ( k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0)))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f215,f92])).

fof(f215,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0)))
    | sK1 = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f211,f96])).

fof(f211,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0)))
    | sK1 = k4_relat_1(sK0) ),
    inference(resolution,[],[f83,f88])).

fof(f83,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_relat_1(sK0)
      | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1))
      | sK1 = X1 ) ),
    inference(forward_demodulation,[],[f82,f40])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1))
      | sK1 = X1 ) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f78,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1))
      | sK1 = X1 ) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17465)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (17464)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (17446)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (17451)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (17462)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (17443)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (17457)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (17456)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (17449)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (17452)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (17445)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (17453)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (17459)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (17447)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (17442)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17447)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f217,f164])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    sK1 != k4_relat_1(sK0)),
% 0.21/0.54    inference(superposition,[],[f41,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f89,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & ! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | ~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (! [X2,X3] : ((k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2) | (~r2_hidden(X3,k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)))) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k2_relat_1(X0) = k1_relat_1(X1) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v1_funct_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f38,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v2_funct_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    sK1 != k2_funct_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f209])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0)))),
% 0.21/0.54    inference(forward_demodulation,[],[f206,f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))))),
% 0.21/0.54    inference(subsumption_resolution,[],[f204,f188])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f187,f164])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f186,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f42,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    ~v1_relat_1(k4_relat_1(sK0)) | r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f182,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f42,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f81,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f87,f42])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f43])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f38,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k4_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0) | r2_hidden(sK2(sK1,X0),k2_relat_1(sK0)) | sK1 = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f80,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    k1_relat_1(sK1) = k2_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1)) | sK1 = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f79,f40])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1)) | sK1 = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f77,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK1) | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1)) | sK1 = X0) )),
% 0.21/0.54    inference(resolution,[],[f37,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    v1_funct_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ~r2_hidden(sK2(sK1,k4_relat_1(sK0)),k2_relat_1(sK0)) | sK2(sK1,k4_relat_1(sK0)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))))),
% 0.21/0.54    inference(resolution,[],[f194,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | ~r2_hidden(X3,k2_relat_1(sK0)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.21/0.54    inference(forward_demodulation,[],[f66,f40])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k2_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.21/0.54    inference(forward_demodulation,[],[f63,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X3] : (~r2_hidden(k1_funct_1(sK1,X3),k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X3)) = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(sK0)) | ~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) != X2 | k1_funct_1(sK0,X2) = X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    r2_hidden(k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))),k2_relat_1(sK1))),
% 0.21/0.54    inference(resolution,[],[f188,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f36])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~v1_relat_1(sK1) | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f37])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))) )),
% 0.21/0.54    inference(superposition,[],[f47,f40])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) = k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0)))))),
% 0.21/0.54    inference(resolution,[],[f194,f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK0),k1_funct_1(sK0,X1)) = X1) )),
% 0.21/0.54    inference(forward_demodulation,[],[f121,f90])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f120,f42])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK0) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f119,f38])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f43])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0) | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X1)) = X1) )),
% 0.21/0.54    inference(superposition,[],[f44,f39])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0))) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f92])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0))) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f211,f96])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    ~v1_relat_1(k4_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) | k1_funct_1(sK1,sK2(sK1,k4_relat_1(sK0))) != k1_funct_1(k4_relat_1(sK0),sK2(sK1,k4_relat_1(sK0))) | sK1 = k4_relat_1(sK0)),
% 0.21/0.54    inference(resolution,[],[f83,f88])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(sK0) | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1)) | sK1 = X1) )),
% 0.21/0.54    inference(forward_demodulation,[],[f82,f40])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(sK1) | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1)) | sK1 = X1) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(sK1) | k1_funct_1(sK1,sK2(sK1,X1)) != k1_funct_1(X1,sK2(sK1,X1)) | sK1 = X1) )),
% 0.21/0.54    inference(resolution,[],[f37,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK2(X0,X1)) != k1_funct_1(X1,sK2(X0,X1)) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (17447)------------------------------
% 0.21/0.54  % (17447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17447)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (17447)Memory used [KB]: 6268
% 0.21/0.54  % (17447)Time elapsed: 0.120 s
% 0.21/0.54  % (17447)------------------------------
% 0.21/0.54  % (17447)------------------------------
% 0.21/0.54  % (17440)Success in time 0.171 s
%------------------------------------------------------------------------------

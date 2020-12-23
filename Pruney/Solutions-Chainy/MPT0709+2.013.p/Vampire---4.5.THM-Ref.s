%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 ( 456 expanded)
%              Number of equality atoms :   48 (  95 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(subsumption_resolution,[],[f207,f38])).

fof(f38,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f207,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f205,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))
      | k10_relat_1(sK1,k9_relat_1(sK1,X1)) = X1 ) ),
    inference(resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f73,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f205,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f204,f64])).

fof(f64,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f204,plain,(
    r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f200,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f200,plain,
    ( r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f191,f72])).

fof(f72,plain,(
    sK0 = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f191,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),k10_relat_1(k5_relat_1(k6_relat_1(X0),sK1),k9_relat_1(sK1,X1)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f189,f34])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(k9_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2))) ) ),
    inference(forward_demodulation,[],[f188,f98])).

fof(f98,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f97,f39])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f97,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2) ),
    inference(subsumption_resolution,[],[f96,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f96,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f93,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f186,f40])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:00:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (19366)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.46  % (19376)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.46  % (19366)Refutation not found, incomplete strategy% (19366)------------------------------
% 0.19/0.46  % (19366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (19366)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (19366)Memory used [KB]: 10618
% 0.19/0.46  % (19366)Time elapsed: 0.046 s
% 0.19/0.46  % (19366)------------------------------
% 0.19/0.46  % (19366)------------------------------
% 0.19/0.47  % (19376)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f207,f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.47    inference(negated_conjecture,[],[f13])).
% 0.19/0.47  fof(f13,conjecture,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.19/0.47  fof(f207,plain,(
% 0.19/0.47    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.19/0.47    inference(resolution,[],[f205,f80])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    ( ! [X1] : (~r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) | k10_relat_1(sK1,k9_relat_1(sK1,X1)) = X1) )),
% 0.19/0.47    inference(resolution,[],[f76,f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(flattening,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f75,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    v1_relat_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f73,f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    v1_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.47    inference(resolution,[],[f50,f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    v2_funct_1(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.19/0.47  fof(f205,plain,(
% 0.19/0.47    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.19/0.47    inference(forward_demodulation,[],[f204,f64])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.19/0.47    inference(resolution,[],[f46,f34])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.19/0.47  fof(f204,plain,(
% 0.19/0.47    r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,sK0)))),
% 0.19/0.47    inference(subsumption_resolution,[],[f200,f59])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.47    inference(equality_resolution,[],[f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f29])).
% 0.19/0.47  fof(f200,plain,(
% 0.19/0.47    r1_tarski(sK0,k10_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1),k9_relat_1(sK1,sK0))) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 0.19/0.47    inference(superposition,[],[f191,f72])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    sK0 = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 0.19/0.47    inference(resolution,[],[f70,f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.19/0.47    inference(resolution,[],[f69,f61])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.19/0.47    inference(equality_resolution,[],[f56])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.47    inference(rectify,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.19/0.47    inference(resolution,[],[f49,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.19/0.47  fof(f191,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),k10_relat_1(k5_relat_1(k6_relat_1(X0),sK1),k9_relat_1(sK1,X1))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 0.19/0.47    inference(resolution,[],[f189,f34])).
% 0.19/0.47  fof(f189,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(k9_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2)))) )),
% 0.19/0.47    inference(forward_demodulation,[],[f188,f98])).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k6_relat_1(X1),X2)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f97,f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f96,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f93,f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f6])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k10_relat_1(k2_funct_1(k6_relat_1(X1)),X2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.19/0.47    inference(resolution,[],[f51,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v2_funct_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2))) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f186,f40])).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(k10_relat_1(k6_relat_1(X0),X2),k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),k9_relat_1(X1,X2))) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.47    inference(superposition,[],[f47,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (19376)------------------------------
% 0.19/0.47  % (19376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (19376)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (19376)Memory used [KB]: 6268
% 0.19/0.47  % (19376)Time elapsed: 0.063 s
% 0.19/0.47  % (19376)------------------------------
% 0.19/0.47  % (19376)------------------------------
% 0.19/0.47  % (19354)Success in time 0.116 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:47:13 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 317 expanded)
%              Number of leaves         :   30 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  398 (1071 expanded)
%              Number of equality atoms :   61 ( 158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f679,plain,(
    $false ),
    inference(subsumption_resolution,[],[f678,f349])).

fof(f349,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f335,f216])).

fof(f216,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f209,f151])).

fof(f151,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_relat_1(sK1))
      | ~ r1_tarski(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f97,f140])).

fof(f140,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f73])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f209,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f169,f62])).

fof(f62,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f169,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f100,f139])).

fof(f139,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f94,f59])).

fof(f59,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f90,f73])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f335,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f318,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f318,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK0))
      | r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f316,f61])).

fof(f61,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f316,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK1))
      | ~ r1_tarski(X0,k2_relat_1(sK0))
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(superposition,[],[f295,f220])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f219,f104])).

fof(f219,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k3_tarski(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f103,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK10(X0,X1,X2))
      | k3_tarski(k2_tarski(X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f93,f73])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK10(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK10(X0,X1,X2))
        & r1_tarski(X2,sK10(X0,X1,X2))
        & r1_tarski(X0,sK10(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK10(X0,X1,X2))
        & r1_tarski(X2,sK10(X0,X1,X2))
        & r1_tarski(X0,sK10(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK10(X0,X1,X2))
      | k3_tarski(k2_tarski(X0,X2)) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f91,f73])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK10(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f295,plain,(
    ! [X2] :
      ( r1_tarski(X2,k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
      | ~ r1_tarski(X2,k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f97,f248])).

fof(f248,plain,(
    k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(sK0))) ),
    inference(resolution,[],[f187,f60])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k3_tarski(k2_tarski(X0,sK0))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(sK0))) ) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f73,f73])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f678,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f673,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f673,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f150,f663])).

fof(f663,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f661,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f64])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f661,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f660,f158])).

fof(f158,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f155,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f155,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f110,f127])).

fof(f127,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f122,f125])).

fof(f125,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f122,f70])).

fof(f122,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f121,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f107,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f107,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK4(X0,X1),X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f110,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f660,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f655,f59])).

fof(f655,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f173,f647])).

fof(f647,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f145,f590])).

fof(f590,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0))) ),
    inference(resolution,[],[f588,f96])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f588,plain,(
    ! [X49] :
      ( ~ r1_tarski(sK1,X49)
      | r1_tarski(sK0,X49) ) ),
    inference(resolution,[],[f241,f61])).

fof(f241,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X10,X9)
      | r1_tarski(X10,X8)
      | ~ r1_tarski(X9,X8) ) ),
    inference(superposition,[],[f97,f220])).

fof(f145,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_tarski(k2_tarski(X4,k1_xboole_0)))
      | k1_xboole_0 = k6_subset_1(X3,X4) ) ),
    inference(resolution,[],[f98,f113])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f88,f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f173,plain,(
    ! [X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f67,f60])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_subset_1(X0,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f99,f140])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f89,f73,f72])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:29:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (19658)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (19649)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (19655)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (19664)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (19659)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (19671)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (19660)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (19668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (19666)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (19647)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (19644)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (19646)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (19650)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (19654)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (19661)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (19645)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.56  % (19659)Refutation not found, incomplete strategy% (19659)------------------------------
% 1.42/0.56  % (19659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (19643)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.56  % (19659)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (19659)Memory used [KB]: 10618
% 1.42/0.56  % (19659)Time elapsed: 0.126 s
% 1.42/0.56  % (19659)------------------------------
% 1.42/0.56  % (19659)------------------------------
% 1.42/0.56  % (19651)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.56  % (19663)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.56  % (19672)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.56  % (19672)Refutation not found, incomplete strategy% (19672)------------------------------
% 1.42/0.56  % (19672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (19672)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (19672)Memory used [KB]: 1663
% 1.42/0.56  % (19672)Time elapsed: 0.100 s
% 1.42/0.56  % (19672)------------------------------
% 1.42/0.56  % (19672)------------------------------
% 1.42/0.56  % (19652)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (19657)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.57  % (19667)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.57  % (19671)Refutation not found, incomplete strategy% (19671)------------------------------
% 1.42/0.57  % (19671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (19671)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (19671)Memory used [KB]: 10746
% 1.42/0.57  % (19671)Time elapsed: 0.136 s
% 1.42/0.57  % (19671)------------------------------
% 1.42/0.57  % (19671)------------------------------
% 1.42/0.57  % (19670)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.57  % (19662)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.57  % (19653)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.58  % (19653)Refutation not found, incomplete strategy% (19653)------------------------------
% 1.42/0.58  % (19653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (19653)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (19653)Memory used [KB]: 10746
% 1.42/0.58  % (19653)Time elapsed: 0.158 s
% 1.42/0.58  % (19653)------------------------------
% 1.42/0.58  % (19653)------------------------------
% 1.62/0.58  % (19648)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.62/0.58  % (19669)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.62/0.58  % (19665)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.62/0.58  % (19656)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.13/0.69  % (19675)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.13/0.70  % (19673)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.13/0.71  % (19665)Refutation found. Thanks to Tanya!
% 2.13/0.71  % SZS status Theorem for theBenchmark
% 2.13/0.71  % SZS output start Proof for theBenchmark
% 2.13/0.71  fof(f679,plain,(
% 2.13/0.71    $false),
% 2.13/0.71    inference(subsumption_resolution,[],[f678,f349])).
% 2.13/0.71  fof(f349,plain,(
% 2.13/0.71    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(resolution,[],[f335,f216])).
% 2.13/0.71  fof(f216,plain,(
% 2.13/0.71    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(resolution,[],[f209,f151])).
% 2.13/0.71  fof(f151,plain,(
% 2.13/0.71    ( ! [X1] : (r1_tarski(X1,k3_relat_1(sK1)) | ~r1_tarski(X1,k2_relat_1(sK1))) )),
% 2.13/0.71    inference(superposition,[],[f97,f140])).
% 2.13/0.71  fof(f140,plain,(
% 2.13/0.71    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.13/0.71    inference(resolution,[],[f94,f60])).
% 2.13/0.71  fof(f60,plain,(
% 2.13/0.71    v1_relat_1(sK1)),
% 2.13/0.71    inference(cnf_transformation,[],[f36])).
% 2.13/0.71  fof(f36,plain,(
% 2.13/0.71    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).
% 2.13/0.71  fof(f34,plain,(
% 2.13/0.71    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f35,plain,(
% 2.13/0.71    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f22,plain,(
% 2.13/0.71    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.13/0.71    inference(flattening,[],[f21])).
% 2.13/0.71  fof(f21,plain,(
% 2.13/0.71    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.13/0.71    inference(ennf_transformation,[],[f20])).
% 2.13/0.71  fof(f20,negated_conjecture,(
% 2.13/0.71    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.13/0.71    inference(negated_conjecture,[],[f19])).
% 2.13/0.71  fof(f19,conjecture,(
% 2.13/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.13/0.71  fof(f94,plain,(
% 2.13/0.71    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.13/0.71    inference(definition_unfolding,[],[f65,f73])).
% 2.13/0.71  fof(f73,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.13/0.71    inference(cnf_transformation,[],[f13])).
% 2.13/0.71  fof(f13,axiom,(
% 2.13/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.13/0.71  fof(f65,plain,(
% 2.13/0.71    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f23])).
% 2.13/0.71  fof(f23,plain,(
% 2.13/0.71    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.13/0.71    inference(ennf_transformation,[],[f16])).
% 2.13/0.71  fof(f16,axiom,(
% 2.13/0.71    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.13/0.71  fof(f97,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f87,f73])).
% 2.13/0.71  fof(f87,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f27])).
% 2.13/0.71  fof(f27,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.13/0.71    inference(ennf_transformation,[],[f5])).
% 2.13/0.71  fof(f5,axiom,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.13/0.71  fof(f209,plain,(
% 2.13/0.71    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(resolution,[],[f169,f62])).
% 2.13/0.71  fof(f62,plain,(
% 2.13/0.71    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(cnf_transformation,[],[f36])).
% 2.13/0.71  fof(f169,plain,(
% 2.13/0.71    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 2.13/0.71    inference(superposition,[],[f100,f139])).
% 2.13/0.71  fof(f139,plain,(
% 2.13/0.71    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.13/0.71    inference(resolution,[],[f94,f59])).
% 2.13/0.71  fof(f59,plain,(
% 2.13/0.71    v1_relat_1(sK0)),
% 2.13/0.71    inference(cnf_transformation,[],[f36])).
% 2.13/0.71  fof(f100,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f90,f73])).
% 2.13/0.71  fof(f90,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f31])).
% 2.13/0.71  fof(f31,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.13/0.71    inference(flattening,[],[f30])).
% 2.13/0.71  fof(f30,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.13/0.71    inference(ennf_transformation,[],[f11])).
% 2.13/0.71  fof(f11,axiom,(
% 2.13/0.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.13/0.71  fof(f335,plain,(
% 2.13/0.71    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.13/0.71    inference(resolution,[],[f318,f104])).
% 2.13/0.71  fof(f104,plain,(
% 2.13/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.13/0.71    inference(equality_resolution,[],[f75])).
% 2.13/0.71  fof(f75,plain,(
% 2.13/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.13/0.71    inference(cnf_transformation,[],[f44])).
% 2.13/0.71  fof(f44,plain,(
% 2.13/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/0.71    inference(flattening,[],[f43])).
% 2.13/0.71  fof(f43,plain,(
% 2.13/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/0.71    inference(nnf_transformation,[],[f4])).
% 2.13/0.71  fof(f4,axiom,(
% 2.13/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.13/0.71  fof(f318,plain,(
% 2.13/0.71    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK0)) | r1_tarski(X0,k2_relat_1(sK1))) )),
% 2.13/0.71    inference(subsumption_resolution,[],[f316,f61])).
% 2.13/0.71  fof(f61,plain,(
% 2.13/0.71    r1_tarski(sK0,sK1)),
% 2.13/0.71    inference(cnf_transformation,[],[f36])).
% 2.13/0.71  fof(f316,plain,(
% 2.13/0.71    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK1)) | ~r1_tarski(X0,k2_relat_1(sK0)) | ~r1_tarski(sK0,sK1)) )),
% 2.13/0.71    inference(superposition,[],[f295,f220])).
% 2.13/0.71  fof(f220,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X1,X0)) )),
% 2.13/0.71    inference(subsumption_resolution,[],[f219,f104])).
% 2.13/0.71  fof(f219,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.13/0.71    inference(duplicate_literal_removal,[],[f217])).
% 2.13/0.71  fof(f217,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k3_tarski(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 2.13/0.71    inference(resolution,[],[f103,f101])).
% 2.13/0.71  fof(f101,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK10(X0,X1,X2)) | k3_tarski(k2_tarski(X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f93,f73])).
% 2.13/0.71  fof(f93,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK10(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f58])).
% 2.13/0.71  fof(f58,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK10(X0,X1,X2)) & r1_tarski(X2,sK10(X0,X1,X2)) & r1_tarski(X0,sK10(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f57])).
% 2.13/0.71  fof(f57,plain,(
% 2.13/0.71    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK10(X0,X1,X2)) & r1_tarski(X2,sK10(X0,X1,X2)) & r1_tarski(X0,sK10(X0,X1,X2))))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f33,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.13/0.71    inference(flattening,[],[f32])).
% 2.13/0.71  fof(f32,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.13/0.71    inference(ennf_transformation,[],[f6])).
% 2.13/0.71  fof(f6,axiom,(
% 2.13/0.71    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 2.13/0.71  fof(f103,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,sK10(X0,X1,X2)) | k3_tarski(k2_tarski(X0,X2)) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f91,f73])).
% 2.13/0.71  fof(f91,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK10(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f58])).
% 2.13/0.71  fof(f295,plain,(
% 2.13/0.71    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) | ~r1_tarski(X2,k2_relat_1(sK0))) )),
% 2.13/0.71    inference(superposition,[],[f97,f248])).
% 2.13/0.71  fof(f248,plain,(
% 2.13/0.71    k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(sK0)))),
% 2.13/0.71    inference(resolution,[],[f187,f60])).
% 2.13/0.71  fof(f187,plain,(
% 2.13/0.71    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k3_tarski(k2_tarski(X0,sK0))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(sK0)))) )),
% 2.13/0.71    inference(resolution,[],[f95,f59])).
% 2.13/0.71  fof(f95,plain,(
% 2.13/0.71    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f66,f73,f73])).
% 2.13/0.71  fof(f66,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f24])).
% 2.13/0.71  fof(f24,plain,(
% 2.13/0.71    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.13/0.71    inference(ennf_transformation,[],[f18])).
% 2.13/0.71  fof(f18,axiom,(
% 2.13/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 2.13/0.71  fof(f678,plain,(
% 2.13/0.71    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(subsumption_resolution,[],[f673,f64])).
% 2.13/0.71  fof(f64,plain,(
% 2.13/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f7])).
% 2.13/0.71  fof(f7,axiom,(
% 2.13/0.71    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.13/0.71  fof(f673,plain,(
% 2.13/0.71    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.13/0.71    inference(superposition,[],[f150,f663])).
% 2.13/0.71  fof(f663,plain,(
% 2.13/0.71    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.13/0.71    inference(resolution,[],[f661,f113])).
% 2.13/0.71  fof(f113,plain,(
% 2.13/0.71    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.13/0.71    inference(resolution,[],[f76,f64])).
% 2.13/0.71  fof(f76,plain,(
% 2.13/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f44])).
% 2.13/0.71  fof(f661,plain,(
% 2.13/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.13/0.71    inference(forward_demodulation,[],[f660,f158])).
% 2.13/0.71  fof(f158,plain,(
% 2.13/0.71    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.13/0.71    inference(resolution,[],[f155,f70])).
% 2.13/0.71  fof(f70,plain,(
% 2.13/0.71    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.13/0.71    inference(cnf_transformation,[],[f42])).
% 2.13/0.71  fof(f42,plain,(
% 2.13/0.71    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f41])).
% 2.13/0.71  fof(f41,plain,(
% 2.13/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f26,plain,(
% 2.13/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.13/0.71    inference(ennf_transformation,[],[f3])).
% 2.13/0.71  fof(f3,axiom,(
% 2.13/0.71    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.13/0.71  fof(f155,plain,(
% 2.13/0.71    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k1_xboole_0))) )),
% 2.13/0.71    inference(resolution,[],[f110,f127])).
% 2.13/0.71  fof(f127,plain,(
% 2.13/0.71    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.13/0.71    inference(backward_demodulation,[],[f122,f125])).
% 2.13/0.71  fof(f125,plain,(
% 2.13/0.71    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 2.13/0.71    inference(resolution,[],[f122,f70])).
% 2.13/0.71  fof(f122,plain,(
% 2.13/0.71    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k1_xboole_0))) )),
% 2.13/0.71    inference(resolution,[],[f121,f63])).
% 2.13/0.71  fof(f63,plain,(
% 2.13/0.71    v1_xboole_0(k1_xboole_0)),
% 2.13/0.71    inference(cnf_transformation,[],[f2])).
% 2.13/0.71  fof(f2,axiom,(
% 2.13/0.71    v1_xboole_0(k1_xboole_0)),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.13/0.71  fof(f121,plain,(
% 2.13/0.71    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k3_tarski(X1))) )),
% 2.13/0.71    inference(resolution,[],[f107,f68])).
% 2.13/0.71  fof(f68,plain,(
% 2.13/0.71    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f40])).
% 2.13/0.71  fof(f40,plain,(
% 2.13/0.71    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.13/0.71  fof(f39,plain,(
% 2.13/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f38,plain,(
% 2.13/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.71    inference(rectify,[],[f37])).
% 2.13/0.71  fof(f37,plain,(
% 2.13/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.71    inference(nnf_transformation,[],[f1])).
% 2.13/0.71  fof(f1,axiom,(
% 2.13/0.71    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.13/0.71  fof(f107,plain,(
% 2.13/0.71    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 2.13/0.71    inference(equality_resolution,[],[f78])).
% 2.13/0.71  fof(f78,plain,(
% 2.13/0.71    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 2.13/0.71    inference(cnf_transformation,[],[f50])).
% 2.13/0.71  fof(f50,plain,(
% 2.13/0.71    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & ((r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f46,f49,f48,f47])).
% 2.13/0.71  fof(f47,plain,(
% 2.13/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) | r2_hidden(sK4(X0,X1),X1))))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f48,plain,(
% 2.13/0.71    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) => (r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f49,plain,(
% 2.13/0.71    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f46,plain,(
% 2.13/0.71    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.13/0.71    inference(rectify,[],[f45])).
% 2.13/0.71  fof(f45,plain,(
% 2.13/0.71    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.13/0.71    inference(nnf_transformation,[],[f12])).
% 2.13/0.71  fof(f12,axiom,(
% 2.13/0.71    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 2.13/0.71  fof(f110,plain,(
% 2.13/0.71    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 2.13/0.71    inference(equality_resolution,[],[f83])).
% 2.13/0.71  fof(f83,plain,(
% 2.13/0.71    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 2.13/0.71    inference(cnf_transformation,[],[f56])).
% 2.13/0.71  fof(f56,plain,(
% 2.13/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.13/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f52,f55,f54,f53])).
% 2.13/0.71  fof(f53,plain,(
% 2.13/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f54,plain,(
% 2.13/0.71    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f55,plain,(
% 2.13/0.71    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 2.13/0.71    introduced(choice_axiom,[])).
% 2.13/0.71  fof(f52,plain,(
% 2.13/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.13/0.71    inference(rectify,[],[f51])).
% 2.13/0.71  fof(f51,plain,(
% 2.13/0.71    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.13/0.71    inference(nnf_transformation,[],[f15])).
% 2.13/0.71  fof(f15,axiom,(
% 2.13/0.71    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.13/0.71  fof(f660,plain,(
% 2.13/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.13/0.71    inference(subsumption_resolution,[],[f655,f59])).
% 2.13/0.71  fof(f655,plain,(
% 2.13/0.71    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 2.13/0.71    inference(superposition,[],[f173,f647])).
% 2.13/0.71  fof(f647,plain,(
% 2.13/0.71    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.13/0.71    inference(resolution,[],[f145,f590])).
% 2.13/0.71  fof(f590,plain,(
% 2.13/0.71    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0)))) )),
% 2.13/0.71    inference(resolution,[],[f588,f96])).
% 2.13/0.71  fof(f96,plain,(
% 2.13/0.71    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 2.13/0.71    inference(definition_unfolding,[],[f71,f73])).
% 2.13/0.71  fof(f71,plain,(
% 2.13/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.13/0.71    inference(cnf_transformation,[],[f10])).
% 2.13/0.71  fof(f10,axiom,(
% 2.13/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.13/0.71  fof(f588,plain,(
% 2.13/0.71    ( ! [X49] : (~r1_tarski(sK1,X49) | r1_tarski(sK0,X49)) )),
% 2.13/0.71    inference(resolution,[],[f241,f61])).
% 2.13/0.71  fof(f241,plain,(
% 2.13/0.71    ( ! [X10,X8,X9] : (~r1_tarski(X10,X9) | r1_tarski(X10,X8) | ~r1_tarski(X9,X8)) )),
% 2.13/0.71    inference(superposition,[],[f97,f220])).
% 2.13/0.71  fof(f145,plain,(
% 2.13/0.71    ( ! [X4,X3] : (~r1_tarski(X3,k3_tarski(k2_tarski(X4,k1_xboole_0))) | k1_xboole_0 = k6_subset_1(X3,X4)) )),
% 2.13/0.71    inference(resolution,[],[f98,f113])).
% 2.13/0.71  fof(f98,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 2.13/0.71    inference(definition_unfolding,[],[f88,f72,f73])).
% 2.13/0.71  fof(f72,plain,(
% 2.13/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f14])).
% 2.13/0.71  fof(f14,axiom,(
% 2.13/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.13/0.71  fof(f88,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.13/0.71    inference(cnf_transformation,[],[f28])).
% 2.13/0.71  fof(f28,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.71    inference(ennf_transformation,[],[f8])).
% 2.13/0.71  fof(f8,axiom,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.13/0.71  fof(f173,plain,(
% 2.13/0.71    ( ! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X1,sK1))) | ~v1_relat_1(X1)) )),
% 2.13/0.71    inference(resolution,[],[f67,f60])).
% 2.13/0.71  fof(f67,plain,(
% 2.13/0.71    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X0)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f25])).
% 2.13/0.71  fof(f25,plain,(
% 2.13/0.71    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.13/0.71    inference(ennf_transformation,[],[f17])).
% 2.13/0.71  fof(f17,axiom,(
% 2.13/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 2.13/0.71  fof(f150,plain,(
% 2.13/0.71    ( ! [X0] : (~r1_tarski(k6_subset_1(X0,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 2.13/0.71    inference(superposition,[],[f99,f140])).
% 2.13/0.71  fof(f99,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.13/0.71    inference(definition_unfolding,[],[f89,f73,f72])).
% 2.13/0.71  fof(f89,plain,(
% 2.13/0.71    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.13/0.71    inference(cnf_transformation,[],[f29])).
% 2.13/0.71  fof(f29,plain,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.13/0.71    inference(ennf_transformation,[],[f9])).
% 2.13/0.71  fof(f9,axiom,(
% 2.13/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.13/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.13/0.71  % SZS output end Proof for theBenchmark
% 2.13/0.71  % (19665)------------------------------
% 2.13/0.71  % (19665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.71  % (19665)Termination reason: Refutation
% 2.13/0.71  
% 2.13/0.71  % (19665)Memory used [KB]: 7036
% 2.13/0.71  % (19665)Time elapsed: 0.274 s
% 2.13/0.71  % (19665)------------------------------
% 2.13/0.71  % (19665)------------------------------
% 2.13/0.71  % (19642)Success in time 0.338 s
%------------------------------------------------------------------------------

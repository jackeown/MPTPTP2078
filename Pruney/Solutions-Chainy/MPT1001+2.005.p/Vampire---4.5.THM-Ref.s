%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 647 expanded)
%              Number of leaves         :   12 ( 152 expanded)
%              Depth                    :   28
%              Number of atoms          :  225 (3013 expanded)
%              Number of equality atoms :   93 (1391 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f131])).

fof(f131,plain,(
    r2_hidden(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f80,f116])).

fof(f116,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f71])).

fof(f71,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f67,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X4] :
          ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
          | ~ r2_hidden(X4,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
            | ~ r2_hidden(X4,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
        & r2_hidden(X3,sK1) )
   => ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f13])).

% (15984)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

fof(f65,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f53,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f115,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f55])).

fof(f55,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k2_relat_1(sK2)
    | r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f106,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
     => ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

fof(f106,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2)))
    | sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f105,f71])).

fof(f105,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2)))
    | r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f97,f55])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,X0)))
      | r1_tarski(sK1,k2_relat_1(X0))
      | sK1 = k2_relat_1(sK2) ) ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | r2_hidden(sK4(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | sK1 = k2_relat_1(sK2)
      | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X4)) ) ),
    inference(forward_demodulation,[],[f88,f52])).

fof(f52,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f88,plain,(
    ! [X4] :
      ( sK1 = k2_relat_1(sK2)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(forward_demodulation,[],[f34,f54])).

fof(f54,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f33,f47])).

fof(f34,plain,(
    ! [X4] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f35,f54])).

fof(f35,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f150,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(forward_demodulation,[],[f149,f116])).

fof(f149,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f148,f55])).

fof(f148,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f39,f141])).

fof(f141,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f138,f33])).

fof(f138,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f132,f49])).

fof(f132,plain,(
    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( sK1 != sK1
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f78,f116])).

fof(f78,plain,
    ( sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f36,f54])).

fof(f36,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (15977)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.49  % (15993)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (15989)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (15972)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (15977)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    r2_hidden(sK3,sK1)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    sK1 != sK1 | r2_hidden(sK3,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f80,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f115,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f67,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f66,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f65,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    (sK1 != k2_relset_1(sK0,sK1,sK2) | (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1)) => (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(rectify,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f13])).
% 0.22/0.51  % (15984)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(superposition,[],[f53,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 0.22/0.51    inference(resolution,[],[f33,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v1_relat_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f33,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | sK1 = k2_relat_1(sK2) | r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.51    inference(superposition,[],[f106,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | (k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) & r2_hidden(sK4(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => (k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1))) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tarski(X0,k2_relat_1(X1)) | ? [X2] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : ~(k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2)) & r2_hidden(X2,X0)) => r1_tarski(X0,k2_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2))) | sK1 = k2_relat_1(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f71])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2))) | r1_tarski(sK1,k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f97,f55])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(sK4(sK1,X0))) | r1_tarski(sK1,k2_relat_1(X0)) | sK1 = k2_relat_1(sK2)) )),
% 0.22/0.51    inference(resolution,[],[f89,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | r2_hidden(sK4(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X4] : (~r2_hidden(X4,sK1) | sK1 = k2_relat_1(sK2) | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X4))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f88,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.22/0.51    inference(resolution,[],[f33,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X4] : (sK1 = k2_relat_1(sK2) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f34,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.51    inference(resolution,[],[f33,f47])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X4] : (sK1 = k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    r2_hidden(sK3,sK1) | sK1 != k2_relat_1(sK2)),
% 0.22/0.51    inference(backward_demodulation,[],[f35,f54])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    r2_hidden(sK3,sK1) | sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~r2_hidden(sK3,sK1)),
% 0.22/0.51    inference(forward_demodulation,[],[f149,f116])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ~r2_hidden(sK3,k2_relat_1(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f55])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.51    inference(superposition,[],[f39,f141])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f33])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(superposition,[],[f132,f49])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    sK1 != sK1 | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.51    inference(backward_demodulation,[],[f78,f116])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    sK1 != k2_relat_1(sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.51    inference(backward_demodulation,[],[f36,f54])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15977)------------------------------
% 0.22/0.51  % (15977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15977)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15977)Memory used [KB]: 1663
% 0.22/0.51  % (15977)Time elapsed: 0.108 s
% 0.22/0.51  % (15977)------------------------------
% 0.22/0.51  % (15977)------------------------------
% 0.22/0.51  % (15971)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (15968)Success in time 0.147 s
%------------------------------------------------------------------------------

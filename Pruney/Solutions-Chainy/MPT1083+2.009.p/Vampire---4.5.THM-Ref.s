%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:17 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 496 expanded)
%              Number of leaves         :   17 ( 173 expanded)
%              Depth                    :   17
%              Number of atoms          :  320 (3225 expanded)
%              Number of equality atoms :   45 ( 455 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f293,plain,(
    $false ),
    inference(global_subsumption,[],[f47,f292])).

fof(f292,plain,(
    ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f286,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK2),X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
            & v1_funct_1(X2)
            & v5_relat_1(X2,sK0)
            & v1_relat_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X1,sK0,sK0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
        & v1_funct_1(X2)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f286,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f285,f193])).

fof(f193,plain,(
    ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f186,f192])).

fof(f192,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f46,f74,f190])).

fof(f190,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f50,f173])).

fof(f173,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f131,f170])).

fof(f170,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(global_subsumption,[],[f91,f169])).

fof(f169,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f168,f120])).

fof(f120,plain,(
    ! [X4] :
      ( ~ v1_partfun1(sK1,X4)
      | ~ v4_relat_1(sK1,X4)
      | k1_relat_1(sK1) = X4 ) ),
    inference(resolution,[],[f60,f74])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f168,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(global_subsumption,[],[f44,f42,f166])).

fof(f166,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f140,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK1,X0)
      | ~ v1_funct_2(sK1,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f66,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f131,plain,(
    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(resolution,[],[f127,f46])).

fof(f127,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k1_relat_1(k5_relat_1(X4,sK1)) = k10_relat_1(X4,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f51,f74])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f74,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f186,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f185,f173])).

fof(f185,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f86,f173])).

fof(f86,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(k5_relat_1(sK2,sK1)),k1_relat_1(sK2)) ),
    inference(extensionality_resolution,[],[f64,f49])).

fof(f49,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

% (29075)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f40,plain,(
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

fof(f285,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X3))
      | ~ r1_tarski(k2_relat_1(sK2),X3) ) ),
    inference(forward_demodulation,[],[f280,f151])).

fof(f151,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f101,f150])).

fof(f150,plain,(
    sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f147,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f147,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f145,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | v4_relat_1(sK2,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f143,f70])).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),X2)
      | ~ r1_tarski(k2_relat_1(sK2),X3)
      | v4_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f137,f66])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f65,f46])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f101,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f280,plain,(
    ! [X3] :
      ( ~ r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),X3)
      | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f219,f70])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_relat_1(sK2))
      | ~ r1_tarski(k9_relat_1(sK2,X2),X3)
      | r1_tarski(X2,k10_relat_1(sK2,X3)) ) ),
    inference(global_subsumption,[],[f46,f216])).

fof(f216,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k9_relat_1(sK2,X2),X3)
      | ~ r1_tarski(X2,k1_relat_1(sK2))
      | r1_tarski(X2,k10_relat_1(sK2,X3))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

% (29066)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f47,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:14:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (29070)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (29058)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (29061)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (29079)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (29080)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (29067)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (29062)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.33/0.54  % (29058)Refutation not found, incomplete strategy% (29058)------------------------------
% 1.33/0.54  % (29058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (29058)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (29058)Memory used [KB]: 10746
% 1.33/0.54  % (29058)Time elapsed: 0.120 s
% 1.33/0.54  % (29058)------------------------------
% 1.33/0.54  % (29058)------------------------------
% 1.33/0.55  % (29081)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.33/0.55  % (29070)Refutation found. Thanks to Tanya!
% 1.33/0.55  % SZS status Theorem for theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f293,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(global_subsumption,[],[f47,f292])).
% 1.33/0.55  fof(f292,plain,(
% 1.33/0.55    ~v5_relat_1(sK2,sK0)),
% 1.33/0.55    inference(resolution,[],[f286,f76])).
% 1.33/0.55  fof(f76,plain,(
% 1.33/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(sK2),X0) | ~v5_relat_1(sK2,X0)) )),
% 1.33/0.55    inference(resolution,[],[f57,f46])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    v1_relat_1(sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    ((k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)) & ~v1_xboole_0(sK0)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f36,f35,f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) & ~v1_xboole_0(sK0))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X1,sK0,sK0) & v1_funct_1(X1)) => (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1)) & v1_funct_1(X2) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f17,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.33/0.55    inference(flattening,[],[f16])).
% 1.33/0.55  fof(f16,plain,(
% 1.33/0.55    ? [X0] : (? [X1] : (? [X2] : (k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1)) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,negated_conjecture,(
% 1.33/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.33/0.55    inference(negated_conjecture,[],[f14])).
% 1.33/0.55  fof(f14,conjecture,(
% 1.33/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f24])).
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.33/0.55  fof(f286,plain,(
% 1.33/0.55    ~r1_tarski(k2_relat_1(sK2),sK0)),
% 1.33/0.55    inference(resolution,[],[f285,f193])).
% 1.33/0.55  fof(f193,plain,(
% 1.33/0.55    ~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))),
% 1.33/0.55    inference(subsumption_resolution,[],[f186,f192])).
% 1.33/0.55  fof(f192,plain,(
% 1.33/0.55    r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2))),
% 1.33/0.55    inference(global_subsumption,[],[f46,f74,f190])).
% 1.33/0.55  fof(f190,plain,(
% 1.33/0.55    r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2)),
% 1.33/0.55    inference(superposition,[],[f50,f173])).
% 1.33/0.55  fof(f173,plain,(
% 1.33/0.55    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,sK0)),
% 1.33/0.55    inference(backward_demodulation,[],[f131,f170])).
% 1.33/0.55  fof(f170,plain,(
% 1.33/0.55    sK0 = k1_relat_1(sK1)),
% 1.33/0.55    inference(global_subsumption,[],[f91,f169])).
% 1.33/0.55  fof(f169,plain,(
% 1.33/0.55    ~v4_relat_1(sK1,sK0) | sK0 = k1_relat_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f168,f120])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    ( ! [X4] : (~v1_partfun1(sK1,X4) | ~v4_relat_1(sK1,X4) | k1_relat_1(sK1) = X4) )),
% 1.33/0.55    inference(resolution,[],[f60,f74])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 1.33/0.55    inference(cnf_transformation,[],[f39])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.33/0.55  fof(f168,plain,(
% 1.33/0.55    v1_partfun1(sK1,sK0)),
% 1.33/0.55    inference(global_subsumption,[],[f44,f42,f166])).
% 1.33/0.55  fof(f166,plain,(
% 1.33/0.55    v1_partfun1(sK1,sK0) | ~v1_funct_2(sK1,sK0,sK0) | v1_xboole_0(sK0)),
% 1.33/0.55    inference(resolution,[],[f140,f45])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f140,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK1,X0) | ~v1_funct_2(sK1,X0,X1) | v1_xboole_0(X1)) )),
% 1.33/0.55    inference(resolution,[],[f55,f43])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    v1_funct_1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.33/0.55    inference(flattening,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ~v1_xboole_0(sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    v1_funct_2(sK1,sK0,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f91,plain,(
% 1.33/0.55    v4_relat_1(sK1,sK0)),
% 1.33/0.55    inference(resolution,[],[f66,f45])).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.33/0.55  fof(f131,plain,(
% 1.33/0.55    k1_relat_1(k5_relat_1(sK2,sK1)) = k10_relat_1(sK2,k1_relat_1(sK1))),
% 1.33/0.55    inference(resolution,[],[f127,f46])).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    ( ! [X4] : (~v1_relat_1(X4) | k1_relat_1(k5_relat_1(X4,sK1)) = k10_relat_1(X4,k1_relat_1(sK1))) )),
% 1.33/0.55    inference(resolution,[],[f51,f74])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f18])).
% 1.33/0.55  fof(f18,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    v1_relat_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f73,f45])).
% 1.33/0.55  fof(f73,plain,(
% 1.33/0.55    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_relat_1(X1)) )),
% 1.33/0.55    inference(resolution,[],[f52,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.33/0.55  fof(f186,plain,(
% 1.33/0.55    ~r1_tarski(k10_relat_1(sK2,sK0),k1_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0))),
% 1.33/0.55    inference(forward_demodulation,[],[f185,f173])).
% 1.33/0.55  fof(f185,plain,(
% 1.33/0.55    ~r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK0)) | ~r1_tarski(k1_relat_1(k5_relat_1(sK2,sK1)),k1_relat_1(sK2))),
% 1.33/0.55    inference(backward_demodulation,[],[f86,f173])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k5_relat_1(sK2,sK1))) | ~r1_tarski(k1_relat_1(k5_relat_1(sK2,sK1)),k1_relat_1(sK2))),
% 1.33/0.55    inference(extensionality_resolution,[],[f64,f49])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(flattening,[],[f40])).
% 1.33/0.55  % (29075)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.55  fof(f285,plain,(
% 1.33/0.55    ( ! [X3] : (r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X3)) | ~r1_tarski(k2_relat_1(sK2),X3)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f280,f151])).
% 1.33/0.55  fof(f151,plain,(
% 1.33/0.55    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.33/0.55    inference(superposition,[],[f101,f150])).
% 1.33/0.55  fof(f150,plain,(
% 1.33/0.55    sK2 = k7_relat_1(sK2,k1_relat_1(sK2))),
% 1.33/0.55    inference(resolution,[],[f147,f104])).
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) )),
% 1.33/0.55    inference(resolution,[],[f59,f46])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f26])).
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.33/0.55  fof(f147,plain,(
% 1.33/0.55    v4_relat_1(sK2,k1_relat_1(sK2))),
% 1.33/0.55    inference(resolution,[],[f145,f70])).
% 1.33/0.55  fof(f70,plain,(
% 1.33/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.55    inference(equality_resolution,[],[f63])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.55    inference(cnf_transformation,[],[f41])).
% 1.33/0.55  fof(f145,plain,(
% 1.33/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v4_relat_1(sK2,k1_relat_1(sK2))) )),
% 1.33/0.55    inference(resolution,[],[f143,f70])).
% 1.33/0.55  fof(f143,plain,(
% 1.33/0.55    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(sK2),X2) | ~r1_tarski(k2_relat_1(sK2),X3) | v4_relat_1(sK2,X2)) )),
% 1.33/0.55    inference(resolution,[],[f137,f66])).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(k1_relat_1(sK2),X1) | ~r1_tarski(k2_relat_1(sK2),X0)) )),
% 1.33/0.55    inference(resolution,[],[f65,f46])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f30])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(flattening,[],[f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.33/0.55  fof(f101,plain,(
% 1.33/0.55    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 1.33/0.55    inference(resolution,[],[f56,f46])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f23])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(ennf_transformation,[],[f5])).
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.33/0.55  fof(f280,plain,(
% 1.33/0.55    ( ! [X3] : (~r1_tarski(k9_relat_1(sK2,k1_relat_1(sK2)),X3) | r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,X3))) )),
% 1.33/0.55    inference(resolution,[],[f219,f70])).
% 1.33/0.55  fof(f219,plain,(
% 1.33/0.55    ( ! [X2,X3] : (~r1_tarski(X2,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X2),X3) | r1_tarski(X2,k10_relat_1(sK2,X3))) )),
% 1.33/0.55    inference(global_subsumption,[],[f46,f216])).
% 1.33/0.55  fof(f216,plain,(
% 1.33/0.55    ( ! [X2,X3] : (~r1_tarski(k9_relat_1(sK2,X2),X3) | ~r1_tarski(X2,k1_relat_1(sK2)) | r1_tarski(X2,k10_relat_1(sK2,X3)) | ~v1_relat_1(sK2)) )),
% 1.33/0.55    inference(resolution,[],[f68,f48])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    v1_funct_1(sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.33/0.55    inference(flattening,[],[f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.33/0.55    inference(ennf_transformation,[],[f9])).
% 1.33/0.55  % (29066)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.33/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    v5_relat_1(sK2,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f37])).
% 1.33/0.55  % SZS output end Proof for theBenchmark
% 1.33/0.55  % (29070)------------------------------
% 1.33/0.55  % (29070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (29070)Termination reason: Refutation
% 1.33/0.55  
% 1.33/0.55  % (29070)Memory used [KB]: 6524
% 1.33/0.55  % (29070)Time elapsed: 0.135 s
% 1.33/0.55  % (29070)------------------------------
% 1.33/0.55  % (29070)------------------------------
% 1.33/0.55  % (29057)Success in time 0.18 s
%------------------------------------------------------------------------------

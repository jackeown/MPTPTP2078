%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:49 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 185 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  257 ( 861 expanded)
%              Number of equality atoms :   48 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f120])).

fof(f120,plain,(
    ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    inference(subsumption_resolution,[],[f119,f114])).

fof(f114,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f79,f113,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f113,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f48,f77])).

fof(f77,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f47,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k2_relset_1(X1,X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k1_relset_1(X1,sK0,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k2_relset_1(X1,sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k2_relset_1(sK1,sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f48,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f56,f47,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f95,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f49,f76])).

fof(f76,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    inference(forward_demodulation,[],[f132,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f132,plain,(
    r2_hidden(sK3(k1_relat_1(sK2)),k3_tarski(k1_zfmisc_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f100,f117,f72])).

fof(f72,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(X6,X0)
      | r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK4(X0,X1),X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f117,plain,(
    r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f114,f55])).

fof(f100,plain,(
    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f94,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f92,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f75,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f75,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.36  ipcrm: permission denied for id (1226670080)
% 0.21/0.37  ipcrm: permission denied for id (1226735618)
% 0.21/0.37  ipcrm: permission denied for id (1233092612)
% 0.21/0.37  ipcrm: permission denied for id (1233190918)
% 0.21/0.37  ipcrm: permission denied for id (1226866695)
% 0.21/0.37  ipcrm: permission denied for id (1226932233)
% 0.21/0.38  ipcrm: permission denied for id (1231028234)
% 0.21/0.38  ipcrm: permission denied for id (1231061003)
% 0.21/0.38  ipcrm: permission denied for id (1227030540)
% 0.21/0.38  ipcrm: permission denied for id (1227063309)
% 0.21/0.38  ipcrm: permission denied for id (1227096078)
% 0.21/0.38  ipcrm: permission denied for id (1231093775)
% 0.21/0.38  ipcrm: permission denied for id (1231126544)
% 0.21/0.38  ipcrm: permission denied for id (1227194385)
% 0.21/0.39  ipcrm: permission denied for id (1231159314)
% 0.21/0.39  ipcrm: permission denied for id (1227259923)
% 0.21/0.39  ipcrm: permission denied for id (1231224853)
% 0.21/0.39  ipcrm: permission denied for id (1231257622)
% 0.21/0.39  ipcrm: permission denied for id (1233322007)
% 0.21/0.39  ipcrm: permission denied for id (1227423768)
% 0.21/0.39  ipcrm: permission denied for id (1233354777)
% 0.21/0.40  ipcrm: permission denied for id (1233420315)
% 0.21/0.40  ipcrm: permission denied for id (1231421468)
% 0.21/0.40  ipcrm: permission denied for id (1227587613)
% 0.21/0.40  ipcrm: permission denied for id (1227620382)
% 0.21/0.40  ipcrm: permission denied for id (1233453087)
% 0.21/0.40  ipcrm: permission denied for id (1227685920)
% 0.21/0.41  ipcrm: permission denied for id (1233518626)
% 0.21/0.41  ipcrm: permission denied for id (1227784227)
% 0.21/0.41  ipcrm: permission denied for id (1231552548)
% 0.21/0.41  ipcrm: permission denied for id (1227849765)
% 0.21/0.41  ipcrm: permission denied for id (1227882534)
% 0.21/0.41  ipcrm: permission denied for id (1227948072)
% 0.21/0.41  ipcrm: permission denied for id (1227980841)
% 0.21/0.42  ipcrm: permission denied for id (1231618090)
% 0.21/0.42  ipcrm: permission denied for id (1228046379)
% 0.21/0.42  ipcrm: permission denied for id (1228079148)
% 0.21/0.42  ipcrm: permission denied for id (1228111917)
% 0.21/0.42  ipcrm: permission denied for id (1231650862)
% 0.21/0.42  ipcrm: permission denied for id (1228210223)
% 0.21/0.42  ipcrm: permission denied for id (1228242992)
% 0.21/0.42  ipcrm: permission denied for id (1228275761)
% 0.21/0.43  ipcrm: permission denied for id (1228308530)
% 0.21/0.43  ipcrm: permission denied for id (1233584179)
% 0.21/0.43  ipcrm: permission denied for id (1231716404)
% 0.21/0.43  ipcrm: permission denied for id (1231749173)
% 0.21/0.43  ipcrm: permission denied for id (1228439606)
% 0.21/0.43  ipcrm: permission denied for id (1228505144)
% 0.21/0.43  ipcrm: permission denied for id (1231814713)
% 0.21/0.44  ipcrm: permission denied for id (1228570682)
% 0.21/0.44  ipcrm: permission denied for id (1228603451)
% 0.21/0.44  ipcrm: permission denied for id (1228636220)
% 0.21/0.44  ipcrm: permission denied for id (1228668989)
% 0.21/0.44  ipcrm: permission denied for id (1228701758)
% 0.21/0.44  ipcrm: permission denied for id (1233649727)
% 0.21/0.44  ipcrm: permission denied for id (1228767296)
% 0.21/0.44  ipcrm: permission denied for id (1228800065)
% 0.21/0.45  ipcrm: permission denied for id (1228832834)
% 0.21/0.45  ipcrm: permission denied for id (1231880259)
% 0.21/0.45  ipcrm: permission denied for id (1231913028)
% 0.21/0.45  ipcrm: permission denied for id (1228931141)
% 0.21/0.45  ipcrm: permission denied for id (1231945798)
% 0.21/0.45  ipcrm: permission denied for id (1231978567)
% 0.21/0.45  ipcrm: permission denied for id (1229029448)
% 0.21/0.45  ipcrm: permission denied for id (1232011337)
% 0.21/0.46  ipcrm: permission denied for id (1229094986)
% 0.21/0.46  ipcrm: permission denied for id (1229127755)
% 0.21/0.46  ipcrm: permission denied for id (1232044108)
% 0.21/0.46  ipcrm: permission denied for id (1229193293)
% 0.21/0.46  ipcrm: permission denied for id (1232109647)
% 0.21/0.46  ipcrm: permission denied for id (1232142416)
% 0.21/0.46  ipcrm: permission denied for id (1229324369)
% 0.21/0.47  ipcrm: permission denied for id (1232175186)
% 0.21/0.47  ipcrm: permission denied for id (1229389907)
% 0.21/0.47  ipcrm: permission denied for id (1232207956)
% 0.21/0.47  ipcrm: permission denied for id (1232273494)
% 0.21/0.47  ipcrm: permission denied for id (1229520983)
% 0.21/0.47  ipcrm: permission denied for id (1232306264)
% 0.21/0.47  ipcrm: permission denied for id (1229586521)
% 0.21/0.48  ipcrm: permission denied for id (1229619290)
% 0.21/0.48  ipcrm: permission denied for id (1232339035)
% 0.21/0.48  ipcrm: permission denied for id (1233748060)
% 0.21/0.48  ipcrm: permission denied for id (1232437342)
% 0.21/0.48  ipcrm: permission denied for id (1229783135)
% 0.21/0.48  ipcrm: permission denied for id (1229815904)
% 0.21/0.48  ipcrm: permission denied for id (1232470113)
% 0.21/0.49  ipcrm: permission denied for id (1232502882)
% 0.21/0.49  ipcrm: permission denied for id (1229914211)
% 0.21/0.49  ipcrm: permission denied for id (1232535652)
% 0.21/0.49  ipcrm: permission denied for id (1229946981)
% 0.21/0.49  ipcrm: permission denied for id (1229979750)
% 0.21/0.49  ipcrm: permission denied for id (1230012519)
% 0.21/0.49  ipcrm: permission denied for id (1230045288)
% 0.21/0.49  ipcrm: permission denied for id (1230078057)
% 0.21/0.50  ipcrm: permission denied for id (1233813610)
% 0.21/0.50  ipcrm: permission denied for id (1232601195)
% 0.21/0.50  ipcrm: permission denied for id (1230176364)
% 0.21/0.50  ipcrm: permission denied for id (1233846381)
% 0.21/0.50  ipcrm: permission denied for id (1230241902)
% 0.21/0.50  ipcrm: permission denied for id (1230307440)
% 0.21/0.51  ipcrm: permission denied for id (1233977458)
% 0.21/0.51  ipcrm: permission denied for id (1230405747)
% 0.21/0.51  ipcrm: permission denied for id (1232765044)
% 0.21/0.51  ipcrm: permission denied for id (1230504054)
% 0.21/0.51  ipcrm: permission denied for id (1234108537)
% 0.21/0.52  ipcrm: permission denied for id (1232928890)
% 0.21/0.52  ipcrm: permission denied for id (1230667899)
% 0.21/0.52  ipcrm: permission denied for id (1232961660)
% 0.21/0.52  ipcrm: permission denied for id (1230733437)
% 0.21/0.52  ipcrm: permission denied for id (1234141310)
% 0.21/0.52  ipcrm: permission denied for id (1230798975)
% 0.63/0.62  % (25876)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.63/0.63  % (25868)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.63/0.63  % (25881)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.63/0.64  % (25873)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.05/0.64  % (25881)Refutation found. Thanks to Tanya!
% 1.05/0.64  % SZS status Theorem for theBenchmark
% 1.05/0.64  % SZS output start Proof for theBenchmark
% 1.05/0.64  fof(f137,plain,(
% 1.05/0.64    $false),
% 1.05/0.64    inference(subsumption_resolution,[],[f136,f120])).
% 1.05/0.64  fof(f120,plain,(
% 1.05/0.64    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 1.05/0.64    inference(subsumption_resolution,[],[f119,f114])).
% 1.05/0.64  fof(f114,plain,(
% 1.05/0.64    k1_xboole_0 != k1_relat_1(sK2)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f79,f113,f52])).
% 1.05/0.64  fof(f52,plain,(
% 1.05/0.64    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f34])).
% 1.05/0.64  fof(f34,plain,(
% 1.05/0.64    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.05/0.64    inference(nnf_transformation,[],[f20])).
% 1.05/0.64  fof(f20,plain,(
% 1.05/0.64    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.05/0.64    inference(ennf_transformation,[],[f11])).
% 1.05/0.64  fof(f11,axiom,(
% 1.05/0.64    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.05/0.64  fof(f113,plain,(
% 1.05/0.64    k1_xboole_0 != k2_relat_1(sK2)),
% 1.05/0.64    inference(superposition,[],[f48,f77])).
% 1.05/0.64  fof(f77,plain,(
% 1.05/0.64    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f47,f69])).
% 1.05/0.64  fof(f69,plain,(
% 1.05/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f27])).
% 1.05/0.64  fof(f27,plain,(
% 1.05/0.64    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.05/0.64    inference(ennf_transformation,[],[f14])).
% 1.05/0.64  fof(f14,axiom,(
% 1.05/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.05/0.64  fof(f47,plain,(
% 1.05/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.05/0.64    inference(cnf_transformation,[],[f33])).
% 1.05/0.64  fof(f33,plain,(
% 1.05/0.64    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.05/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32,f31,f30])).
% 1.05/0.64  fof(f30,plain,(
% 1.05/0.64    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f31,plain,(
% 1.05/0.64    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f32,plain,(
% 1.05/0.64    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f19,plain,(
% 1.05/0.64    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.05/0.64    inference(flattening,[],[f18])).
% 1.05/0.64  fof(f18,plain,(
% 1.05/0.64    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.05/0.64    inference(ennf_transformation,[],[f16])).
% 1.05/0.64  fof(f16,negated_conjecture,(
% 1.05/0.64    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.05/0.64    inference(negated_conjecture,[],[f15])).
% 1.05/0.64  fof(f15,conjecture,(
% 1.05/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 1.05/0.64  fof(f48,plain,(
% 1.05/0.64    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 1.05/0.64    inference(cnf_transformation,[],[f33])).
% 1.05/0.64  fof(f79,plain,(
% 1.05/0.64    v1_relat_1(sK2)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f56,f47,f54])).
% 1.05/0.64  fof(f54,plain,(
% 1.05/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f21])).
% 1.05/0.64  fof(f21,plain,(
% 1.05/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.05/0.64    inference(ennf_transformation,[],[f8])).
% 1.05/0.64  fof(f8,axiom,(
% 1.05/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.05/0.64  fof(f56,plain,(
% 1.05/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.05/0.64    inference(cnf_transformation,[],[f10])).
% 1.05/0.64  fof(f10,axiom,(
% 1.05/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.05/0.64  fof(f119,plain,(
% 1.05/0.64    k1_xboole_0 = k1_relat_1(sK2) | ~r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 1.05/0.64    inference(resolution,[],[f95,f59])).
% 1.05/0.64  fof(f59,plain,(
% 1.05/0.64    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f24])).
% 1.05/0.64  fof(f24,plain,(
% 1.05/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.05/0.64    inference(ennf_transformation,[],[f5])).
% 1.05/0.64  fof(f5,axiom,(
% 1.05/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.05/0.64  fof(f95,plain,(
% 1.05/0.64    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | k1_xboole_0 = k1_relat_1(sK2)),
% 1.05/0.64    inference(resolution,[],[f86,f55])).
% 1.05/0.64  fof(f55,plain,(
% 1.05/0.64    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.05/0.64    inference(cnf_transformation,[],[f36])).
% 1.05/0.64  fof(f36,plain,(
% 1.05/0.64    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.05/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f35])).
% 1.05/0.64  fof(f35,plain,(
% 1.05/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f22,plain,(
% 1.05/0.64    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.05/0.64    inference(ennf_transformation,[],[f1])).
% 1.05/0.64  fof(f1,axiom,(
% 1.05/0.64    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.05/0.64  fof(f86,plain,(
% 1.05/0.64    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.05/0.64    inference(backward_demodulation,[],[f49,f76])).
% 1.05/0.64  fof(f76,plain,(
% 1.05/0.64    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f47,f70])).
% 1.05/0.64  fof(f70,plain,(
% 1.05/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f28])).
% 1.05/0.64  fof(f28,plain,(
% 1.05/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.05/0.64    inference(ennf_transformation,[],[f13])).
% 1.05/0.64  fof(f13,axiom,(
% 1.05/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.05/0.64  fof(f49,plain,(
% 1.05/0.64    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f33])).
% 1.05/0.64  fof(f136,plain,(
% 1.05/0.64    r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 1.05/0.64    inference(forward_demodulation,[],[f132,f51])).
% 1.05/0.64  fof(f51,plain,(
% 1.05/0.64    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.05/0.64    inference(cnf_transformation,[],[f3])).
% 1.05/0.64  fof(f3,axiom,(
% 1.05/0.64    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.05/0.64  fof(f132,plain,(
% 1.05/0.64    r2_hidden(sK3(k1_relat_1(sK2)),k3_tarski(k1_zfmisc_1(sK1)))),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f100,f117,f72])).
% 1.05/0.64  fof(f72,plain,(
% 1.05/0.64    ( ! [X6,X0,X5] : (~r2_hidden(X6,X0) | r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X5,X6)) )),
% 1.05/0.64    inference(equality_resolution,[],[f63])).
% 1.05/0.64  fof(f63,plain,(
% 1.05/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 1.05/0.64    inference(cnf_transformation,[],[f43])).
% 1.05/0.64  fof(f43,plain,(
% 1.05/0.64    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & ((r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.05/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 1.05/0.64  fof(f40,plain,(
% 1.05/0.64    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) | r2_hidden(sK4(X0,X1),X1))))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f41,plain,(
% 1.05/0.64    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) => (r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f42,plain,(
% 1.05/0.64    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))))),
% 1.05/0.64    introduced(choice_axiom,[])).
% 1.05/0.64  fof(f39,plain,(
% 1.05/0.64    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.05/0.64    inference(rectify,[],[f38])).
% 1.05/0.64  fof(f38,plain,(
% 1.05/0.64    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 1.05/0.64    inference(nnf_transformation,[],[f2])).
% 1.05/0.64  fof(f2,axiom,(
% 1.05/0.64    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.05/0.64  fof(f117,plain,(
% 1.05/0.64    r2_hidden(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f114,f55])).
% 1.05/0.64  fof(f100,plain,(
% 1.05/0.64    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f50,f94,f60])).
% 1.05/0.64  fof(f60,plain,(
% 1.05/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f26])).
% 1.05/0.64  fof(f26,plain,(
% 1.05/0.64    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.05/0.64    inference(flattening,[],[f25])).
% 1.05/0.64  fof(f25,plain,(
% 1.05/0.64    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.05/0.64    inference(ennf_transformation,[],[f6])).
% 1.05/0.64  fof(f6,axiom,(
% 1.05/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.05/0.64  fof(f94,plain,(
% 1.05/0.64    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f92,f68])).
% 1.05/0.64  fof(f68,plain,(
% 1.05/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f44])).
% 1.05/0.64  fof(f44,plain,(
% 1.05/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.05/0.64    inference(nnf_transformation,[],[f7])).
% 1.05/0.64  fof(f7,axiom,(
% 1.05/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.05/0.64  fof(f92,plain,(
% 1.05/0.64    r1_tarski(k1_relat_1(sK2),sK1)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f79,f75,f57])).
% 1.05/0.64  fof(f57,plain,(
% 1.05/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f37])).
% 1.05/0.64  fof(f37,plain,(
% 1.05/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.05/0.64    inference(nnf_transformation,[],[f23])).
% 1.05/0.64  fof(f23,plain,(
% 1.05/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.05/0.64    inference(ennf_transformation,[],[f9])).
% 1.05/0.64  fof(f9,axiom,(
% 1.05/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.05/0.64  fof(f75,plain,(
% 1.05/0.64    v4_relat_1(sK2,sK1)),
% 1.05/0.64    inference(unit_resulting_resolution,[],[f47,f71])).
% 1.05/0.64  fof(f71,plain,(
% 1.05/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.05/0.64    inference(cnf_transformation,[],[f29])).
% 1.05/0.64  fof(f29,plain,(
% 1.05/0.64    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.05/0.64    inference(ennf_transformation,[],[f17])).
% 1.05/0.64  fof(f17,plain,(
% 1.05/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.05/0.64    inference(pure_predicate_removal,[],[f12])).
% 1.05/0.64  fof(f12,axiom,(
% 1.05/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.05/0.64  fof(f50,plain,(
% 1.05/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.05/0.64    inference(cnf_transformation,[],[f4])).
% 1.05/0.64  fof(f4,axiom,(
% 1.05/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.05/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.05/0.64  % SZS output end Proof for theBenchmark
% 1.05/0.64  % (25881)------------------------------
% 1.05/0.64  % (25881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.64  % (25881)Termination reason: Refutation
% 1.05/0.64  
% 1.05/0.64  % (25881)Memory used [KB]: 6140
% 1.05/0.64  % (25881)Time elapsed: 0.038 s
% 1.05/0.64  % (25881)------------------------------
% 1.05/0.64  % (25881)------------------------------
% 1.05/0.64  % (25877)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.05/0.64  % (25711)Success in time 0.285 s
%------------------------------------------------------------------------------

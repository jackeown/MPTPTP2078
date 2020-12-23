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
% DateTime   : Thu Dec  3 12:57:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 362 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  212 (1550 expanded)
%              Number of equality atoms :   29 ( 242 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f147,f133])).

fof(f133,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f122,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f122,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f110,f111])).

fof(f111,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f108,f43])).

fof(f108,plain,(
    v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f107,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f107,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(sK3(k1_relat_1(sK2)),k1_relat_1(sK2))
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f105,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_relat_1(sK2))
      | v1_xboole_0(k1_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f94,f91])).

fof(f91,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).

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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(backward_demodulation,[],[f61,f91])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_relset_1(sK1,sK0,sK2))
      | v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(resolution,[],[f49,f42])).

fof(f42,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f105,plain,
    ( m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f104,f46])).

fof(f104,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_relat_1(sK2))
      | v1_xboole_0(k1_relat_1(sK2))
      | m1_subset_1(X3,sK1) ) ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f70,f63])).

fof(f63,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f68,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f68,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X4)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X3,X5)
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f110,plain,(
    v1_xboole_0(k2_relat_1(k1_relat_1(sK2))) ),
    inference(resolution,[],[f108,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f147,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f85,f139])).

fof(f139,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f137,f43])).

fof(f137,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f109,f63])).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f108,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f85,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f41,f83])).

fof(f83,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (26781)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.46  % (26773)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.46  % (26773)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f172,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f171])).
% 0.19/0.46  fof(f171,plain,(
% 0.19/0.46    k1_xboole_0 != k1_xboole_0),
% 0.19/0.46    inference(superposition,[],[f147,f133])).
% 0.19/0.46  fof(f133,plain,(
% 0.19/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(resolution,[],[f122,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.19/0.46    inference(backward_demodulation,[],[f110,f111])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f108,f43])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    v1_xboole_0(k1_relat_1(sK2))),
% 0.19/0.46    inference(resolution,[],[f107,f46])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    ~m1_subset_1(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | v1_xboole_0(k1_relat_1(sK2))),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f106])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    v1_xboole_0(k1_relat_1(sK2)) | ~m1_subset_1(sK3(k1_relat_1(sK2)),k1_relat_1(sK2)) | v1_xboole_0(k1_relat_1(sK2))),
% 0.19/0.46    inference(resolution,[],[f105,f97])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X0,k1_relat_1(sK2)) | v1_xboole_0(k1_relat_1(sK2))) )),
% 0.19/0.46    inference(forward_demodulation,[],[f94,f91])).
% 0.19/0.46  fof(f91,plain,(
% 0.19/0.46    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f54,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ((! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f32,f31,f30])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,sK0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) & ~v1_xboole_0(sK1))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.19/0.46    inference(negated_conjecture,[],[f13])).
% 0.19/0.46  fof(f13,conjecture,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_relat_1(sK2)) | ~m1_subset_1(X0,sK1) | v1_xboole_0(k1_relset_1(sK1,sK0,sK2))) )),
% 0.19/0.46    inference(backward_demodulation,[],[f61,f91])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X0,k1_relset_1(sK1,sK0,sK2)) | v1_xboole_0(k1_relset_1(sK1,sK0,sK2))) )),
% 0.19/0.46    inference(resolution,[],[f49,f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.46  fof(f105,plain,(
% 0.19/0.46    m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.19/0.46    inference(resolution,[],[f104,f46])).
% 0.19/0.46  fof(f104,plain,(
% 0.19/0.46    ( ! [X3] : (~m1_subset_1(X3,k1_relat_1(sK2)) | v1_xboole_0(k1_relat_1(sK2)) | m1_subset_1(X3,sK1)) )),
% 0.19/0.46    inference(resolution,[],[f89,f71])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.46    inference(resolution,[],[f70,f63])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    v1_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f52,f40])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ~v1_relat_1(sK2) | r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.46    inference(resolution,[],[f68,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(nnf_transformation,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    v4_relat_1(sK2,sK1)),
% 0.19/0.46    inference(resolution,[],[f55,f40])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.46  fof(f89,plain,(
% 0.19/0.46    ( ! [X4,X5,X3] : (~r1_tarski(X5,X4) | v1_xboole_0(X5) | ~m1_subset_1(X3,X5) | m1_subset_1(X3,X4)) )),
% 0.19/0.46    inference(resolution,[],[f81,f51])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.46    inference(nnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(X2,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0)) )),
% 0.19/0.46    inference(resolution,[],[f57,f49])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    v1_xboole_0(k2_relat_1(k1_relat_1(sK2)))),
% 0.19/0.46    inference(resolution,[],[f108,f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.19/0.46  fof(f147,plain,(
% 0.19/0.46    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.19/0.46    inference(backward_demodulation,[],[f85,f139])).
% 0.19/0.46  fof(f139,plain,(
% 0.19/0.46    k1_xboole_0 = sK2),
% 0.19/0.46    inference(resolution,[],[f137,f43])).
% 0.19/0.46  fof(f137,plain,(
% 0.19/0.46    v1_xboole_0(sK2)),
% 0.19/0.46    inference(resolution,[],[f109,f63])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    ~v1_relat_1(sK2) | v1_xboole_0(sK2)),
% 0.19/0.46    inference(resolution,[],[f108,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.19/0.46    inference(flattening,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    k1_xboole_0 != k2_relat_1(sK2)),
% 0.19/0.46    inference(superposition,[],[f41,f83])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.19/0.46    inference(resolution,[],[f53,f40])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (26773)------------------------------
% 0.19/0.46  % (26773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (26773)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (26773)Memory used [KB]: 1663
% 0.19/0.46  % (26773)Time elapsed: 0.059 s
% 0.19/0.46  % (26773)------------------------------
% 0.19/0.46  % (26773)------------------------------
% 0.19/0.46  % (26763)Success in time 0.111 s
%------------------------------------------------------------------------------

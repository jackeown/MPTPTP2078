%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:32 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 411 expanded)
%              Number of leaves         :   18 ( 136 expanded)
%              Depth                    :   17
%              Number of atoms          :  199 (1705 expanded)
%              Number of equality atoms :   36 ( 288 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(subsumption_resolution,[],[f440,f368])).

fof(f368,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f43,f366])).

fof(f366,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f349,f235])).

fof(f235,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK2) ),
    inference(resolution,[],[f148,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f148,plain,(
    v1_xboole_0(k8_relat_1(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f138,f129])).

fof(f129,plain,(
    k1_xboole_0 = k8_relat_1(sK4,sK2) ),
    inference(resolution,[],[f113,f46])).

fof(f113,plain,(
    v1_xboole_0(k8_relat_1(sK4,sK2)) ),
    inference(resolution,[],[f80,f61])).

fof(f61,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f38])).

fof(f38,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k8_relat_1(X0,sK2)) ) ),
    inference(resolution,[],[f71,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f138,plain,(
    v1_xboole_0(k8_relat_1(k8_relat_1(sK4,sK2),sK2)) ),
    inference(resolution,[],[f113,f80])).

fof(f349,plain,(
    sK2 = k8_relat_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f82,f332])).

fof(f332,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f329,f46])).

fof(f329,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_relat_1(sK2))
      | v1_xboole_0(k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f96,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f96,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f93,f76])).

fof(f76,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f44,f69])).

fof(f69,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f44,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f75,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f68,f69])).

fof(f68,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f82,plain,(
    sK2 = k8_relat_1(k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f43,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f440,plain,(
    k1_xboole_0 = k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f369,f199])).

fof(f199,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f140,f46])).

fof(f140,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f130,f129])).

fof(f130,plain,(
    v1_xboole_0(k1_relat_1(k8_relat_1(sK4,sK2))) ),
    inference(resolution,[],[f113,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f369,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f70,f366])).

fof(f70,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (798326784)
% 0.12/0.36  ipcrm: permission denied for id (798359553)
% 0.12/0.37  ipcrm: permission denied for id (798490635)
% 0.12/0.37  ipcrm: permission denied for id (798523405)
% 0.12/0.38  ipcrm: permission denied for id (798588947)
% 0.12/0.38  ipcrm: permission denied for id (798654486)
% 0.12/0.39  ipcrm: permission denied for id (798752796)
% 0.12/0.39  ipcrm: permission denied for id (798851103)
% 0.21/0.40  ipcrm: permission denied for id (798949414)
% 0.21/0.41  ipcrm: permission denied for id (799014952)
% 0.21/0.42  ipcrm: permission denied for id (799080496)
% 0.21/0.42  ipcrm: permission denied for id (799113265)
% 0.21/0.42  ipcrm: permission denied for id (799146034)
% 0.21/0.42  ipcrm: permission denied for id (799178806)
% 0.21/0.43  ipcrm: permission denied for id (799244344)
% 0.21/0.43  ipcrm: permission denied for id (799309881)
% 0.21/0.43  ipcrm: permission denied for id (799342651)
% 0.21/0.44  ipcrm: permission denied for id (799408198)
% 0.21/0.44  ipcrm: permission denied for id (799440967)
% 0.21/0.45  ipcrm: permission denied for id (799506507)
% 0.21/0.46  ipcrm: permission denied for id (799670358)
% 0.21/0.46  ipcrm: permission denied for id (799703127)
% 0.21/0.47  ipcrm: permission denied for id (799834207)
% 0.21/0.48  ipcrm: permission denied for id (799866978)
% 0.21/0.49  ipcrm: permission denied for id (800063593)
% 0.21/0.50  ipcrm: permission denied for id (800161912)
% 0.21/0.50  ipcrm: permission denied for id (800194682)
% 0.21/0.51  ipcrm: permission denied for id (800292990)
% 0.21/0.59  % (2215)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.60  % (2215)Refutation not found, incomplete strategy% (2215)------------------------------
% 0.21/0.60  % (2215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (2215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (2215)Memory used [KB]: 10618
% 0.21/0.60  % (2215)Time elapsed: 0.062 s
% 0.21/0.60  % (2215)------------------------------
% 0.21/0.60  % (2215)------------------------------
% 0.91/0.61  % (2231)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.91/0.62  % (2223)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.15/0.63  % (2223)Refutation found. Thanks to Tanya!
% 1.15/0.63  % SZS status Theorem for theBenchmark
% 1.15/0.63  % SZS output start Proof for theBenchmark
% 1.15/0.63  fof(f441,plain,(
% 1.15/0.63    $false),
% 1.15/0.63    inference(subsumption_resolution,[],[f440,f368])).
% 1.15/0.63  fof(f368,plain,(
% 1.15/0.63    k1_xboole_0 != k1_relset_1(sK0,sK1,k1_xboole_0)),
% 1.15/0.63    inference(backward_demodulation,[],[f43,f366])).
% 1.15/0.63  fof(f366,plain,(
% 1.15/0.63    k1_xboole_0 = sK2),
% 1.15/0.63    inference(forward_demodulation,[],[f349,f235])).
% 1.15/0.63  fof(f235,plain,(
% 1.15/0.63    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK2)),
% 1.15/0.63    inference(resolution,[],[f148,f46])).
% 1.15/0.63  fof(f46,plain,(
% 1.15/0.63    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.15/0.63    inference(cnf_transformation,[],[f19])).
% 1.15/0.63  fof(f19,plain,(
% 1.15/0.63    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.15/0.63    inference(ennf_transformation,[],[f1])).
% 1.15/0.63  fof(f1,axiom,(
% 1.15/0.63    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.15/0.63  fof(f148,plain,(
% 1.15/0.63    v1_xboole_0(k8_relat_1(k1_xboole_0,sK2))),
% 1.15/0.63    inference(forward_demodulation,[],[f138,f129])).
% 1.15/0.63  fof(f129,plain,(
% 1.15/0.63    k1_xboole_0 = k8_relat_1(sK4,sK2)),
% 1.15/0.63    inference(resolution,[],[f113,f46])).
% 1.15/0.63  fof(f113,plain,(
% 1.15/0.63    v1_xboole_0(k8_relat_1(sK4,sK2))),
% 1.15/0.63    inference(resolution,[],[f80,f61])).
% 1.15/0.63  fof(f61,plain,(
% 1.15/0.63    v1_xboole_0(sK4)),
% 1.15/0.63    inference(cnf_transformation,[],[f39])).
% 1.15/0.63  fof(f39,plain,(
% 1.15/0.63    v1_xboole_0(sK4)),
% 1.15/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f38])).
% 1.15/0.63  fof(f38,plain,(
% 1.15/0.63    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 1.15/0.63    introduced(choice_axiom,[])).
% 1.15/0.63  fof(f2,axiom,(
% 1.15/0.63    ? [X0] : v1_xboole_0(X0)),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 1.15/0.63  fof(f80,plain,(
% 1.15/0.63    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k8_relat_1(X0,sK2))) )),
% 1.15/0.63    inference(resolution,[],[f71,f53])).
% 1.15/0.63  fof(f53,plain,(
% 1.15/0.63    ( ! [X0,X1] : (v1_xboole_0(k8_relat_1(X1,X0)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 1.15/0.63    inference(cnf_transformation,[],[f23])).
% 1.15/0.63  fof(f23,plain,(
% 1.15/0.63    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 1.15/0.63    inference(flattening,[],[f22])).
% 1.15/0.63  fof(f22,plain,(
% 1.15/0.63    ! [X0,X1] : ((v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 1.15/0.63    inference(ennf_transformation,[],[f8])).
% 1.15/0.63  fof(f8,axiom,(
% 1.15/0.63    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k8_relat_1(X1,X0)) & v1_xboole_0(k8_relat_1(X1,X0))))),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc18_relat_1)).
% 1.15/0.63  fof(f71,plain,(
% 1.15/0.63    v1_relat_1(sK2)),
% 1.15/0.63    inference(resolution,[],[f42,f56])).
% 1.15/0.63  fof(f56,plain,(
% 1.15/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/0.63    inference(cnf_transformation,[],[f25])).
% 1.15/0.63  fof(f25,plain,(
% 1.15/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.15/0.63    inference(ennf_transformation,[],[f10])).
% 1.15/0.63  fof(f10,axiom,(
% 1.15/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.15/0.63  fof(f42,plain,(
% 1.15/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.15/0.63    inference(cnf_transformation,[],[f34])).
% 1.15/0.63  fof(f34,plain,(
% 1.15/0.63    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.15/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32,f31])).
% 1.15/0.63  fof(f31,plain,(
% 1.15/0.63    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.15/0.63    introduced(choice_axiom,[])).
% 1.15/0.63  fof(f32,plain,(
% 1.15/0.63    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 1.15/0.63    introduced(choice_axiom,[])).
% 1.15/0.63  fof(f33,plain,(
% 1.15/0.63    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.15/0.63    introduced(choice_axiom,[])).
% 1.15/0.63  fof(f17,plain,(
% 1.15/0.63    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.15/0.63    inference(flattening,[],[f16])).
% 1.15/0.63  fof(f16,plain,(
% 1.15/0.63    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.15/0.63    inference(ennf_transformation,[],[f15])).
% 1.15/0.63  fof(f15,negated_conjecture,(
% 1.15/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.15/0.63    inference(negated_conjecture,[],[f14])).
% 1.15/0.63  fof(f14,conjecture,(
% 1.15/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 1.15/0.63  fof(f138,plain,(
% 1.15/0.63    v1_xboole_0(k8_relat_1(k8_relat_1(sK4,sK2),sK2))),
% 1.15/0.63    inference(resolution,[],[f113,f80])).
% 1.15/0.63  fof(f349,plain,(
% 1.15/0.63    sK2 = k8_relat_1(k1_xboole_0,sK2)),
% 1.15/0.63    inference(backward_demodulation,[],[f82,f332])).
% 1.15/0.63  fof(f332,plain,(
% 1.15/0.63    k1_xboole_0 = k2_relat_1(sK2)),
% 1.15/0.63    inference(resolution,[],[f329,f46])).
% 1.15/0.63  fof(f329,plain,(
% 1.15/0.63    v1_xboole_0(k2_relat_1(sK2))),
% 1.15/0.63    inference(resolution,[],[f103,f48])).
% 1.15/0.63  fof(f48,plain,(
% 1.15/0.63    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 1.15/0.63    inference(cnf_transformation,[],[f36])).
% 1.15/0.63  fof(f36,plain,(
% 1.15/0.63    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 1.15/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f35])).
% 1.15/0.63  fof(f35,plain,(
% 1.15/0.63    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 1.15/0.63    introduced(choice_axiom,[])).
% 1.15/0.63  fof(f5,axiom,(
% 1.15/0.63    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.15/0.63  fof(f103,plain,(
% 1.15/0.63    ( ! [X0] : (~m1_subset_1(X0,k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2))) )),
% 1.15/0.63    inference(resolution,[],[f96,f49])).
% 1.15/0.63  fof(f49,plain,(
% 1.15/0.63    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.15/0.63    inference(cnf_transformation,[],[f37])).
% 1.15/0.63  fof(f37,plain,(
% 1.15/0.63    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.15/0.63    inference(nnf_transformation,[],[f21])).
% 1.15/0.63  fof(f21,plain,(
% 1.15/0.63    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.15/0.63    inference(ennf_transformation,[],[f4])).
% 1.15/0.63  fof(f4,axiom,(
% 1.15/0.63    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.15/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.15/0.63  fof(f96,plain,(
% 1.15/0.63    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.15/0.63    inference(subsumption_resolution,[],[f93,f76])).
% 1.15/0.63  fof(f76,plain,(
% 1.15/0.63    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.15/0.63    inference(backward_demodulation,[],[f44,f69])).
% 1.15/0.63  fof(f69,plain,(
% 1.15/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.15/0.63    inference(resolution,[],[f42,f58])).
% 1.15/0.63  fof(f58,plain,(
% 1.15/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/0.63    inference(cnf_transformation,[],[f27])).
% 1.15/0.63  fof(f27,plain,(
% 1.15/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.15/0.63    inference(ennf_transformation,[],[f13])).
% 1.15/0.64  fof(f13,axiom,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.15/0.64  fof(f44,plain,(
% 1.15/0.64    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.15/0.64    inference(cnf_transformation,[],[f34])).
% 1.15/0.64  fof(f93,plain,(
% 1.15/0.64    ( ! [X0] : (m1_subset_1(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.15/0.64    inference(resolution,[],[f75,f60])).
% 1.15/0.64  fof(f60,plain,(
% 1.15/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.15/0.64    inference(cnf_transformation,[],[f30])).
% 1.15/0.64  fof(f30,plain,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.15/0.64    inference(flattening,[],[f29])).
% 1.15/0.64  fof(f29,plain,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.15/0.64    inference(ennf_transformation,[],[f6])).
% 1.15/0.64  fof(f6,axiom,(
% 1.15/0.64    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.15/0.64  fof(f75,plain,(
% 1.15/0.64    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.15/0.64    inference(backward_demodulation,[],[f68,f69])).
% 1.15/0.64  fof(f68,plain,(
% 1.15/0.64    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))),
% 1.15/0.64    inference(resolution,[],[f42,f59])).
% 1.15/0.64  fof(f59,plain,(
% 1.15/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/0.64    inference(cnf_transformation,[],[f28])).
% 1.15/0.64  fof(f28,plain,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.15/0.64    inference(ennf_transformation,[],[f11])).
% 1.15/0.64  fof(f11,axiom,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.15/0.64  fof(f82,plain,(
% 1.15/0.64    sK2 = k8_relat_1(k2_relat_1(sK2),sK2)),
% 1.15/0.64    inference(resolution,[],[f71,f45])).
% 1.15/0.64  fof(f45,plain,(
% 1.15/0.64    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.15/0.64    inference(cnf_transformation,[],[f18])).
% 1.15/0.64  fof(f18,plain,(
% 1.15/0.64    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.15/0.64    inference(ennf_transformation,[],[f9])).
% 1.15/0.64  fof(f9,axiom,(
% 1.15/0.64    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 1.15/0.64  fof(f43,plain,(
% 1.15/0.64    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 1.15/0.64    inference(cnf_transformation,[],[f34])).
% 1.15/0.64  fof(f440,plain,(
% 1.15/0.64    k1_xboole_0 = k1_relset_1(sK0,sK1,k1_xboole_0)),
% 1.15/0.64    inference(forward_demodulation,[],[f369,f199])).
% 1.15/0.64  fof(f199,plain,(
% 1.15/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.15/0.64    inference(resolution,[],[f140,f46])).
% 1.15/0.64  fof(f140,plain,(
% 1.15/0.64    v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 1.15/0.64    inference(forward_demodulation,[],[f130,f129])).
% 1.15/0.64  fof(f130,plain,(
% 1.15/0.64    v1_xboole_0(k1_relat_1(k8_relat_1(sK4,sK2)))),
% 1.15/0.64    inference(resolution,[],[f113,f47])).
% 1.15/0.64  fof(f47,plain,(
% 1.15/0.64    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.15/0.64    inference(cnf_transformation,[],[f20])).
% 1.15/0.64  fof(f20,plain,(
% 1.15/0.64    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.15/0.64    inference(ennf_transformation,[],[f7])).
% 1.15/0.64  fof(f7,axiom,(
% 1.15/0.64    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.15/0.64  fof(f369,plain,(
% 1.15/0.64    k1_relat_1(k1_xboole_0) = k1_relset_1(sK0,sK1,k1_xboole_0)),
% 1.15/0.64    inference(backward_demodulation,[],[f70,f366])).
% 1.15/0.64  fof(f70,plain,(
% 1.15/0.64    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.15/0.64    inference(resolution,[],[f42,f57])).
% 1.15/0.64  fof(f57,plain,(
% 1.15/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.15/0.64    inference(cnf_transformation,[],[f26])).
% 1.15/0.64  fof(f26,plain,(
% 1.15/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.15/0.64    inference(ennf_transformation,[],[f12])).
% 1.15/0.64  fof(f12,axiom,(
% 1.15/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.15/0.64  % SZS output end Proof for theBenchmark
% 1.15/0.64  % (2223)------------------------------
% 1.15/0.64  % (2223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.64  % (2223)Termination reason: Refutation
% 1.15/0.64  
% 1.15/0.64  % (2223)Memory used [KB]: 1791
% 1.15/0.64  % (2223)Time elapsed: 0.092 s
% 1.15/0.64  % (2223)------------------------------
% 1.15/0.64  % (2223)------------------------------
% 1.15/0.64  % (2029)Success in time 0.287 s
%------------------------------------------------------------------------------

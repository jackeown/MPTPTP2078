%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 206 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  212 ( 660 expanded)
%              Number of equality atoms :   38 ( 147 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f522,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f180,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ5_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f54,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f180,plain,(
    ~ sQ5_eqProxy(k2_relset_1(sK0,sK1,sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f176,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f176,plain,(
    ~ sQ5_eqProxy(k2_relat_1(sK2),k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f137,f83,f149,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ5_eqProxy(X2,X3)
      | ~ sQ5_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f149,plain,(
    ~ r2_hidden(sK3(k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f147,f40])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f147,plain,(
    m1_subset_1(sK3(k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f102,f137,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f102,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f100,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f100,plain,(
    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f98,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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

fof(f98,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f91,f97,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f97,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f45,f38,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f83,plain,(
    ! [X0] : sQ5_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f137,plain,(
    r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f130,f63])).

fof(f63,plain,(
    ! [X0] :
      ( sQ5_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f44,f59])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f130,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f91,f129,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ sQ5_eqProxy(k1_xboole_0,k2_relat_1(X0))
      | sQ5_eqProxy(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f42,f59,f59])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f129,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f125,f84])).

fof(f125,plain,(
    ~ sQ5_eqProxy(k1_relat_1(sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f86,f116,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ5_eqProxy(X1,X2)
      | ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f116,plain,(
    sQ5_eqProxy(k1_relset_1(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_proxy_replacement,[],[f53,f59])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f86,plain,(
    ~ sQ5_eqProxy(k1_relset_1(sK0,sK1,sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f60,f84])).

fof(f60,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,k1_relset_1(sK0,sK1,sK2)) ),
    inference(equality_proxy_replacement,[],[f39,f59])).

fof(f39,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 19:26:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (808189952)
% 0.14/0.38  ipcrm: permission denied for id (808255491)
% 0.14/0.38  ipcrm: permission denied for id (808288261)
% 0.14/0.38  ipcrm: permission denied for id (808321030)
% 0.14/0.39  ipcrm: permission denied for id (808353799)
% 0.14/0.39  ipcrm: permission denied for id (808419337)
% 0.14/0.39  ipcrm: permission denied for id (808452107)
% 0.14/0.39  ipcrm: permission denied for id (808484876)
% 0.14/0.40  ipcrm: permission denied for id (808583185)
% 0.14/0.40  ipcrm: permission denied for id (808615954)
% 0.21/0.40  ipcrm: permission denied for id (808779799)
% 0.21/0.41  ipcrm: permission denied for id (808812568)
% 0.21/0.41  ipcrm: permission denied for id (808845337)
% 0.21/0.41  ipcrm: permission denied for id (808878106)
% 0.21/0.41  ipcrm: permission denied for id (808910875)
% 0.21/0.41  ipcrm: permission denied for id (808943644)
% 0.21/0.41  ipcrm: permission denied for id (809009181)
% 0.21/0.42  ipcrm: permission denied for id (809074720)
% 0.21/0.42  ipcrm: permission denied for id (809271334)
% 0.21/0.43  ipcrm: permission denied for id (809304103)
% 0.21/0.43  ipcrm: permission denied for id (809435178)
% 0.21/0.43  ipcrm: permission denied for id (809500716)
% 0.21/0.43  ipcrm: permission denied for id (809533485)
% 0.21/0.44  ipcrm: permission denied for id (809697330)
% 0.21/0.44  ipcrm: permission denied for id (809762868)
% 0.21/0.44  ipcrm: permission denied for id (809828406)
% 0.21/0.45  ipcrm: permission denied for id (809861175)
% 0.21/0.45  ipcrm: permission denied for id (809893944)
% 0.21/0.45  ipcrm: permission denied for id (809959482)
% 0.21/0.45  ipcrm: permission denied for id (810057790)
% 0.21/0.46  ipcrm: permission denied for id (810090559)
% 0.21/0.46  ipcrm: permission denied for id (810123328)
% 0.21/0.46  ipcrm: permission denied for id (810156097)
% 0.21/0.46  ipcrm: permission denied for id (810319942)
% 0.21/0.47  ipcrm: permission denied for id (810352711)
% 0.21/0.47  ipcrm: permission denied for id (810385480)
% 0.21/0.47  ipcrm: permission denied for id (810418249)
% 0.21/0.47  ipcrm: permission denied for id (810451018)
% 0.21/0.47  ipcrm: permission denied for id (810483787)
% 0.21/0.47  ipcrm: permission denied for id (810516556)
% 0.21/0.48  ipcrm: permission denied for id (810582095)
% 0.21/0.48  ipcrm: permission denied for id (810647633)
% 0.21/0.48  ipcrm: permission denied for id (810680402)
% 0.21/0.48  ipcrm: permission denied for id (810745940)
% 0.21/0.49  ipcrm: permission denied for id (810877016)
% 0.21/0.49  ipcrm: permission denied for id (810909785)
% 0.21/0.49  ipcrm: permission denied for id (810942554)
% 0.21/0.50  ipcrm: permission denied for id (811073631)
% 0.21/0.50  ipcrm: permission denied for id (811171938)
% 0.21/0.50  ipcrm: permission denied for id (811204707)
% 0.21/0.51  ipcrm: permission denied for id (811368552)
% 0.21/0.51  ipcrm: permission denied for id (811434091)
% 0.21/0.51  ipcrm: permission denied for id (811565167)
% 0.21/0.52  ipcrm: permission denied for id (811696243)
% 0.21/0.52  ipcrm: permission denied for id (811761782)
% 0.21/0.52  ipcrm: permission denied for id (811794551)
% 0.21/0.52  ipcrm: permission denied for id (811827320)
% 0.21/0.53  ipcrm: permission denied for id (812023934)
% 0.21/0.53  ipcrm: permission denied for id (812056703)
% 0.21/0.59  % (27140)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.60  % (27140)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f522,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f38,f180,f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ5_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))) )),
% 0.21/0.60    inference(equality_proxy_replacement,[],[f54,f59])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.60    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.60    inference(ennf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.60  fof(f180,plain,(
% 0.21/0.60    ~sQ5_eqProxy(k2_relset_1(sK0,sK1,sK2),k2_relat_1(sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f176,f84])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X1,X0)) )),
% 0.21/0.60    inference(equality_proxy_axiom,[],[f59])).
% 0.21/0.60  fof(f176,plain,(
% 0.21/0.60    ~sQ5_eqProxy(k2_relat_1(sK2),k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f137,f83,f149,f76])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~sQ5_eqProxy(X2,X3) | ~sQ5_eqProxy(X0,X1) | r2_hidden(X1,X3)) )),
% 0.21/0.60    inference(equality_proxy_axiom,[],[f59])).
% 0.21/0.60  fof(f149,plain,(
% 0.21/0.60    ~r2_hidden(sK3(k2_relat_1(sK2)),k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f147,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.60    inference(flattening,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.60    inference(ennf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.60  fof(f13,negated_conjecture,(
% 0.21/0.60    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.60    inference(negated_conjecture,[],[f12])).
% 0.21/0.60  fof(f12,conjecture,(
% 0.21/0.60    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.60  fof(f147,plain,(
% 0.21/0.60    m1_subset_1(sK3(k2_relat_1(sK2)),sK1)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f102,f137,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.60  fof(f102,plain,(
% 0.21/0.60    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f100,f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.60  fof(f100,plain,(
% 0.21/0.60    r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f98,f57])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(rectify,[],[f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f2])).
% 0.21/0.61  fof(f2,axiom,(
% 0.21/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.61  fof(f98,plain,(
% 0.21/0.61    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f91,f97,f46])).
% 0.21/0.61  fof(f46,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(nnf_transformation,[],[f21])).
% 0.21/0.61  fof(f21,plain,(
% 0.21/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f6])).
% 0.21/0.61  fof(f6,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.61  fof(f97,plain,(
% 0.21/0.61    v5_relat_1(sK2,sK1)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f38,f55])).
% 0.21/0.61  fof(f55,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f25])).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f15])).
% 0.21/0.61  fof(f15,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.61    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.61  fof(f9,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.61  fof(f91,plain,(
% 0.21/0.61    v1_relat_1(sK2)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f45,f38,f43])).
% 0.21/0.61  fof(f43,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f19])).
% 0.21/0.61  fof(f19,plain,(
% 0.21/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(ennf_transformation,[],[f5])).
% 0.21/0.61  fof(f5,axiom,(
% 0.21/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.61  fof(f45,plain,(
% 0.21/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f7])).
% 0.21/0.61  fof(f7,axiom,(
% 0.21/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.61  fof(f83,plain,(
% 0.21/0.61    ( ! [X0] : (sQ5_eqProxy(X0,X0)) )),
% 0.21/0.61    inference(equality_proxy_axiom,[],[f59])).
% 0.21/0.61  fof(f137,plain,(
% 0.21/0.61    r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f130,f63])).
% 0.21/0.61  fof(f63,plain,(
% 0.21/0.61    ( ! [X0] : (sQ5_eqProxy(k1_xboole_0,X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.61    inference(equality_proxy_replacement,[],[f44,f59])).
% 0.21/0.61  fof(f44,plain,(
% 0.21/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f32])).
% 0.21/0.61  fof(f32,plain,(
% 0.21/0.61    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.61    inference(ennf_transformation,[],[f1])).
% 0.21/0.61  fof(f1,axiom,(
% 0.21/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.61  fof(f130,plain,(
% 0.21/0.61    ~sQ5_eqProxy(k1_xboole_0,k2_relat_1(sK2))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f91,f129,f61])).
% 0.21/0.61  fof(f61,plain,(
% 0.21/0.61    ( ! [X0] : (~sQ5_eqProxy(k1_xboole_0,k2_relat_1(X0)) | sQ5_eqProxy(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(equality_proxy_replacement,[],[f42,f59,f59])).
% 0.21/0.61  fof(f42,plain,(
% 0.21/0.61    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f30])).
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(nnf_transformation,[],[f18])).
% 0.21/0.61  fof(f18,plain,(
% 0.21/0.61    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(ennf_transformation,[],[f8])).
% 0.21/0.61  fof(f8,axiom,(
% 0.21/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.61  fof(f129,plain,(
% 0.21/0.61    ~sQ5_eqProxy(k1_xboole_0,k1_relat_1(sK2))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f125,f84])).
% 0.21/0.61  fof(f125,plain,(
% 0.21/0.61    ~sQ5_eqProxy(k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f86,f116,f85])).
% 0.21/0.61  fof(f85,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~sQ5_eqProxy(X1,X2) | ~sQ5_eqProxy(X0,X1) | sQ5_eqProxy(X0,X2)) )),
% 0.21/0.61    inference(equality_proxy_axiom,[],[f59])).
% 0.21/0.61  fof(f116,plain,(
% 0.21/0.61    sQ5_eqProxy(k1_relset_1(sK0,sK1,sK2),k1_relat_1(sK2))),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f38,f66])).
% 0.21/0.61  fof(f66,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (sQ5_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(equality_proxy_replacement,[],[f53,f59])).
% 0.21/0.61  fof(f53,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  fof(f23,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.61    inference(ennf_transformation,[],[f10])).
% 0.21/0.61  fof(f10,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.61  fof(f86,plain,(
% 0.21/0.61    ~sQ5_eqProxy(k1_relset_1(sK0,sK1,sK2),k1_xboole_0)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f60,f84])).
% 0.21/0.61  fof(f60,plain,(
% 0.21/0.61    ~sQ5_eqProxy(k1_xboole_0,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.61    inference(equality_proxy_replacement,[],[f39,f59])).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.61    inference(cnf_transformation,[],[f29])).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.61    inference(cnf_transformation,[],[f29])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (27140)------------------------------
% 0.21/0.61  % (27140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (27140)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (27140)Memory used [KB]: 11001
% 0.21/0.61  % (27140)Time elapsed: 0.018 s
% 0.21/0.61  % (27140)------------------------------
% 0.21/0.61  % (27140)------------------------------
% 0.21/0.61  % (26987)Success in time 0.237 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 12:57:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 313 expanded)
%              Number of leaves         :   18 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          :  248 (1271 expanded)
%              Number of equality atoms :   50 ( 228 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1205,f69])).

fof(f69,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f67,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f67,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1205,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1203,f78])).

fof(f78,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1203,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f1202,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1202,plain,(
    ~ r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1199,f137])).

fof(f137,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f69])).

fof(f136,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f134,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f134,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f40])).

% (20475)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f133,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f41,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1199,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f1167])).

fof(f1167,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(superposition,[],[f1055,f1012])).

fof(f1012,plain,
    ( k1_xboole_0 = k2_relat_1(k2_relat_1(k1_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f983,f116])).

fof(f116,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f114,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f114,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f113,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,k4_tarski(sK5(X7,X6),X6))
      | ~ r2_hidden(X6,k2_relat_1(X7)) ) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f983,plain,(
    ! [X11] :
      ( r2_hidden(sK3(k2_relat_1(k1_relat_1(sK2)),X11),X11)
      | k2_relat_1(k2_relat_1(k1_relat_1(sK2))) = X11
      | ~ r1_tarski(k1_relat_1(sK2),sK1) ) ),
    inference(resolution,[],[f54,f146])).

fof(f146,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,k2_relat_1(k1_relat_1(sK2)))
      | ~ r1_tarski(k1_relat_1(sK2),sK1) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X15] :
      ( ~ r2_hidden(X15,k2_relat_1(k1_relat_1(sK2)))
      | ~ r1_tarski(k1_relat_1(sK2),sK1)
      | ~ r2_hidden(X15,k2_relat_1(k1_relat_1(sK2))) ) ),
    inference(resolution,[],[f112,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_tarski(sK5(k1_relat_1(sK2),X0),X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(k1_relat_1(sK2))) ) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_tarski(sK5(k1_relat_1(sK2),X0),X0),sK1)
      | ~ r2_hidden(X0,k2_relat_1(k1_relat_1(sK2)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f111,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k4_tarski(sK5(k1_relset_1(sK1,sK0,sK2),X2),X2),sK1)
      | ~ r2_hidden(X2,k2_relat_1(k1_relset_1(sK1,sK0,sK2))) ) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k4_tarski(sK5(X4,X3),X3),X5)
      | ~ r2_hidden(X3,k2_relat_1(X4))
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f64,f99])).

fof(f99,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | m1_subset_1(X1,X2)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f62,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1055,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_relat_1(k1_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f1013,f1010])).

fof(f1010,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_relat_1(k1_relat_1(sK2))) = X0
      | ~ r1_tarski(k1_relat_1(sK2),sK1)
      | m1_subset_1(sK3(k2_relat_1(k1_relat_1(sK2)),X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f983,f99])).

fof(f1013,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_relat_1(k1_relat_1(sK2)))
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK3(k2_relat_1(k1_relat_1(sK2)),k1_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f983,f120])).

fof(f120,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ m1_subset_1(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f118,f40])).

fof(f118,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ m1_subset_1(X1,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f42,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:29:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (20473)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.45  % (20459)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.46  % (20457)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (20471)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.47  % (20473)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f1206,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f1205,f69])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    v1_relat_1(sK2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f67,f49])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.19/0.47    inference(resolution,[],[f48,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.47    inference(flattening,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f15])).
% 0.19/0.47  fof(f15,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.19/0.47    inference(negated_conjecture,[],[f14])).
% 0.19/0.47  fof(f14,conjecture,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.47  fof(f1205,plain,(
% 0.19/0.47    ~v1_relat_1(sK2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f1203,f78])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    v4_relat_1(sK2,sK1)),
% 0.19/0.47    inference(resolution,[],[f61,f40])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.47    inference(ennf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.47  fof(f1203,plain,(
% 0.19/0.47    ~v4_relat_1(sK2,sK1) | ~v1_relat_1(sK2)),
% 0.19/0.47    inference(resolution,[],[f1202,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.47  fof(f1202,plain,(
% 0.19/0.47    ~r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.47    inference(subsumption_resolution,[],[f1199,f137])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(sK2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f136,f69])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f135])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.48    inference(superposition,[],[f134,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.19/0.48  fof(f134,plain,(
% 0.19/0.48    k1_xboole_0 != k2_relat_1(sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f133,f40])).
% 0.19/0.48  % (20475)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    k1_xboole_0 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.48    inference(superposition,[],[f41,f60])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f30])).
% 0.19/0.48  fof(f1199,plain,(
% 0.19/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f1167])).
% 0.19/0.48  fof(f1167,plain,(
% 0.19/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK1) | ~r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.48    inference(superposition,[],[f1055,f1012])).
% 0.19/0.48  fof(f1012,plain,(
% 0.19/0.48    k1_xboole_0 = k2_relat_1(k2_relat_1(k1_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.48    inference(resolution,[],[f983,f116])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f114,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.48    inference(cnf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.19/0.48    inference(resolution,[],[f113,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.48  fof(f113,plain,(
% 0.19/0.48    ( ! [X6,X7] : (~r1_tarski(X7,k4_tarski(sK5(X7,X6),X6)) | ~r2_hidden(X6,k2_relat_1(X7))) )),
% 0.19/0.48    inference(resolution,[],[f64,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.19/0.48    inference(equality_resolution,[],[f52])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f37,f36,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.48    inference(rectify,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.19/0.48  fof(f983,plain,(
% 0.19/0.48    ( ! [X11] : (r2_hidden(sK3(k2_relat_1(k1_relat_1(sK2)),X11),X11) | k2_relat_1(k2_relat_1(k1_relat_1(sK2))) = X11 | ~r1_tarski(k1_relat_1(sK2),sK1)) )),
% 0.19/0.48    inference(resolution,[],[f54,f146])).
% 0.19/0.48  fof(f146,plain,(
% 0.19/0.48    ( ! [X15] : (~r2_hidden(X15,k2_relat_1(k1_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),sK1)) )),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f145])).
% 0.19/0.48  fof(f145,plain,(
% 0.19/0.48    ( ! [X15] : (~r2_hidden(X15,k2_relat_1(k1_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),sK1) | ~r2_hidden(X15,k2_relat_1(k1_relat_1(sK2)))) )),
% 0.19/0.48    inference(resolution,[],[f112,f119])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(k4_tarski(sK5(k1_relat_1(sK2),X0),X0),sK1) | ~r2_hidden(X0,k2_relat_1(k1_relat_1(sK2)))) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f117,f40])).
% 0.19/0.48  fof(f117,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(k4_tarski(sK5(k1_relat_1(sK2),X0),X0),sK1) | ~r2_hidden(X0,k2_relat_1(k1_relat_1(sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 0.19/0.48    inference(superposition,[],[f111,f59])).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    ( ! [X2] : (~m1_subset_1(k4_tarski(sK5(k1_relset_1(sK1,sK0,sK2),X2),X2),sK1) | ~r2_hidden(X2,k2_relat_1(k1_relset_1(sK1,sK0,sK2)))) )),
% 0.19/0.48    inference(resolution,[],[f64,f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f30])).
% 0.19/0.48  fof(f112,plain,(
% 0.19/0.48    ( ! [X4,X5,X3] : (m1_subset_1(k4_tarski(sK5(X4,X3),X3),X5) | ~r2_hidden(X3,k2_relat_1(X4)) | ~r1_tarski(X4,X5)) )),
% 0.19/0.48    inference(resolution,[],[f64,f99])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    ( ! [X2,X3,X1] : (~r2_hidden(X1,X3) | m1_subset_1(X1,X2) | ~r1_tarski(X3,X2)) )),
% 0.19/0.48    inference(resolution,[],[f62,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.48    inference(nnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f38])).
% 0.19/0.48  fof(f1055,plain,(
% 0.19/0.48    k1_relat_1(sK2) = k2_relat_1(k2_relat_1(k1_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f1013,f1010])).
% 0.19/0.48  fof(f1010,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k2_relat_1(k2_relat_1(k1_relat_1(sK2))) = X0 | ~r1_tarski(k1_relat_1(sK2),sK1) | m1_subset_1(sK3(k2_relat_1(k1_relat_1(sK2)),X0),X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(resolution,[],[f983,f99])).
% 0.19/0.48  fof(f1013,plain,(
% 0.19/0.48    k1_relat_1(sK2) = k2_relat_1(k2_relat_1(k1_relat_1(sK2))) | ~r1_tarski(k1_relat_1(sK2),sK1) | ~m1_subset_1(sK3(k2_relat_1(k1_relat_1(sK2)),k1_relat_1(sK2)),sK1)),
% 0.19/0.48    inference(resolution,[],[f983,f120])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | ~m1_subset_1(X1,sK1)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f118,f40])).
% 0.19/0.48  fof(f118,plain,(
% 0.19/0.48    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | ~m1_subset_1(X1,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 0.19/0.48    inference(superposition,[],[f42,f59])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (20473)------------------------------
% 0.19/0.48  % (20473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (20473)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (20473)Memory used [KB]: 1791
% 0.19/0.48  % (20473)Time elapsed: 0.035 s
% 0.19/0.48  % (20473)------------------------------
% 0.19/0.48  % (20473)------------------------------
% 0.19/0.48  % (20475)Refutation not found, incomplete strategy% (20475)------------------------------
% 0.19/0.48  % (20475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (20454)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.48  % (20458)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (20447)Success in time 0.131 s
%------------------------------------------------------------------------------

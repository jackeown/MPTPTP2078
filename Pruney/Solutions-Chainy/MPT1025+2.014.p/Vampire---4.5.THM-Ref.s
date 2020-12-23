%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 (1658 expanded)
%              Number of leaves         :   18 ( 458 expanded)
%              Depth                    :   30
%              Number of atoms          :  509 (8589 expanded)
%              Number of equality atoms :   30 (1174 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(subsumption_resolution,[],[f372,f349])).

fof(f349,plain,(
    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f347,f128])).

fof(f128,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f113,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f109,f94])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f109,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f97,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

% (15640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (15657)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (15636)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (15632)Refutation not found, incomplete strategy% (15632)------------------------------
% (15632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15632)Termination reason: Refutation not found, incomplete strategy

% (15632)Memory used [KB]: 10874
% (15632)Time elapsed: 0.120 s
% (15632)------------------------------
% (15632)------------------------------
% (15639)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (15648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f97,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f57,f91])).

fof(f91,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f56,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f57,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f347,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f318,f97])).

fof(f318,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f317,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f153,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f153,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f149,f56])).

fof(f149,plain,(
    ! [X0] :
      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f84,f91])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f317,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f316,f163])).

fof(f163,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f148,f63])).

fof(f148,plain,(
    r2_hidden(sK4,sK1) ),
    inference(resolution,[],[f144,f93])).

fof(f93,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f56,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f144,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,X0)
      | r2_hidden(sK4,X0) ) ),
    inference(backward_demodulation,[],[f136,f143])).

fof(f143,plain,(
    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f142,f94])).

fof(f142,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f139,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f112,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

% (15647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f112,plain,(
    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f108,f94])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f97,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0)
      | ~ v5_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f135,f94])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0)
      | ~ v5_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0)
      | ~ v1_funct_1(sK3)
      | ~ v5_relat_1(sK3,X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f111,plain,(
    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f97,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f316,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f154,f256])).

fof(f256,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f238,f63])).

fof(f238,plain,(
    r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),sK0) ),
    inference(resolution,[],[f197,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f115,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f115,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f114,f94])).

fof(f114,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f92,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f56,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,(
    r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f191,f94])).

fof(f191,plain,
    ( r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f172,f73])).

fof(f172,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,k1_relat_1(sK3))) ),
    inference(resolution,[],[f147,f111])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | r2_hidden(sK4,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f146,f94])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f140,f111])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(sK4,sK2,sK3),X0)
      | r2_hidden(sK4,k9_relat_1(sK3,X0))
      | ~ r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f112,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f154,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f150,f56])).

fof(f150,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f59,f91])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

% (15642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK5(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK5(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK5(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK5(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f372,plain,(
    ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(subsumption_resolution,[],[f371,f334])).

fof(f334,plain,(
    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f332,f128])).

fof(f332,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f312,f97])).

fof(f312,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f311,f164])).

fof(f311,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f310,f163])).

fof(f310,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f160,f256])).

% (15647)Refutation not found, incomplete strategy% (15647)------------------------------
% (15647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15647)Termination reason: Refutation not found, incomplete strategy

% (15647)Memory used [KB]: 10618
% (15647)Time elapsed: 0.120 s
% (15647)------------------------------
% (15647)------------------------------
fof(f160,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f61,f91])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f371,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f370])).

fof(f370,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) ),
    inference(superposition,[],[f58,f365])).

fof(f365,plain,(
    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f364,f94])).

fof(f364,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f358,f55])).

fof(f358,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f354,f81])).

fof(f354,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) ),
    inference(subsumption_resolution,[],[f352,f128])).

fof(f352,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f315,f97])).

fof(f315,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f314,f164])).

% (15641)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f314,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f313,f163])).

fof(f313,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f157,f256])).

fof(f157,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f151,f56])).

fof(f151,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f60,f91])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (15638)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (15632)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (15654)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (15634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (15630)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (15646)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (15633)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (15653)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (15638)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (15644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (15631)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (15643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f373,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f372,f349])).
% 0.22/0.52  fof(f349,plain,(
% 0.22/0.52    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f347,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ~v1_xboole_0(sK2)),
% 0.22/0.52    inference(resolution,[],[f113,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f109,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f56,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f36,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f97,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f50,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(rectify,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  % (15640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (15657)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (15636)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (15632)Refutation not found, incomplete strategy% (15632)------------------------------
% 0.22/0.53  % (15632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15632)Memory used [KB]: 10874
% 0.22/0.53  % (15632)Time elapsed: 0.120 s
% 0.22/0.53  % (15632)------------------------------
% 0.22/0.53  % (15632)------------------------------
% 0.22/0.53  % (15639)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (15648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.53    inference(backward_demodulation,[],[f57,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.22/0.53    inference(resolution,[],[f56,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | v1_xboole_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f318,f97])).
% 0.22/0.53  fof(f318,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f317,f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | m1_subset_1(X0,sK1)) )),
% 0.22/0.53    inference(resolution,[],[f153,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f149,f56])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.22/0.53    inference(superposition,[],[f84,f91])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f316,f163])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(resolution,[],[f148,f63])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    r2_hidden(sK4,sK1)),
% 0.22/0.53    inference(resolution,[],[f144,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    v5_relat_1(sK3,sK1)),
% 0.22/0.53    inference(resolution,[],[f56,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X0] : (~v5_relat_1(sK3,X0) | r2_hidden(sK4,X0)) )),
% 0.22/0.53    inference(backward_demodulation,[],[f136,f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f94])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f139,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK7(sK4,sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f112,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  % (15647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f108,f94])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK7(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f97,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0) | ~v5_relat_1(sK3,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f135,f94])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f131,f55])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK7(sK4,sK2,sK3)),X0) | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f111,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f94])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f97,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f316,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f154,f256])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f238,f63])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),sK0)),
% 0.22/0.53    inference(resolution,[],[f197,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f115,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f114,f94])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f92,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    v4_relat_1(sK3,sK0)),
% 0.22/0.53    inference(resolution,[],[f56,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),k1_relat_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f191,f94])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    r2_hidden(sK7(sK4,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f172,f73])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    r2_hidden(sK4,k9_relat_1(sK3,k1_relat_1(sK3)))),
% 0.22/0.53    inference(resolution,[],[f147,f111])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),X0) | r2_hidden(sK4,k9_relat_1(sK3,X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f94])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),X0) | r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f111])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK7(sK4,sK2,sK3),X0) | r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f112,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f150,f56])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(superposition,[],[f59,f91])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  % (15642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(rectify,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f371,f334])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f332,f128])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | v1_xboole_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f312,f97])).
% 0.22/0.53  fof(f312,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | v1_xboole_0(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f311,f164])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | v1_xboole_0(X5)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f310,f163])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f256])).
% 0.22/0.53  % (15647)Refutation not found, incomplete strategy% (15647)------------------------------
% 0.22/0.53  % (15647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15647)Memory used [KB]: 10618
% 0.22/0.53  % (15647)Time elapsed: 0.120 s
% 0.22/0.53  % (15647)------------------------------
% 0.22/0.53  % (15647)------------------------------
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f152,f56])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(superposition,[],[f61,f91])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(sK5(X1,X2,X3,X4),X1) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f370])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    sK4 != sK4 | ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)),
% 0.22/0.53    inference(superposition,[],[f58,f365])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))),
% 0.22/0.53    inference(subsumption_resolution,[],[f364,f94])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f358,f55])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f354,f81])).
% 0.22/0.53  fof(f354,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f352,f128])).
% 0.22/0.53  fof(f352,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | v1_xboole_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f315,f97])).
% 0.22/0.53  fof(f315,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | v1_xboole_0(X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f314,f164])).
% 0.22/0.53  % (15641)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | v1_xboole_0(X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f313,f163])).
% 0.22/0.53  fof(f313,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f157,f256])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f151,f56])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 0.22/0.53    inference(superposition,[],[f60,f91])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.53  % (15638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15638)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15638)Memory used [KB]: 10874
% 0.22/0.53  % (15638)Time elapsed: 0.111 s
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.53  % (15638)------------------------------
% 0.22/0.53  % (15652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (15629)Success in time 0.174 s
%------------------------------------------------------------------------------

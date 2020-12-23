%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 248 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   20
%              Number of atoms          :  294 (1218 expanded)
%              Number of equality atoms :  163 ( 749 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(equality_resolution,[],[f428])).

fof(f428,plain,(
    ! [X0] : sK2 != X0 ),
    inference(subsumption_resolution,[],[f427,f315])).

fof(f315,plain,(
    ! [X39,X38,X40] :
      ( ~ v1_relat_1(k1_tarski(X40))
      | X39 != X40
      | sK2 != X38
      | X38 != X39 ) ),
    inference(resolution,[],[f261,f61])).

fof(f61,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f59,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f261,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X5,X6)
      | X3 != X4
      | X4 != X5
      | sK2 != X3
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f239,f97])).

% (25860)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (25854)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (25855)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (25866)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k1_tarski(X1))
      | X0 != X1
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f90,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | v1_relat_1(k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | v1_relat_1(k1_tarski(X0))
      | v1_relat_1(k1_tarski(X0)) ) ),
    inference(superposition,[],[f39,f85])).

fof(f85,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | v1_relat_1(k1_tarski(X1)) ) ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f22])).

% (25873)Refutation not found, incomplete strategy% (25873)------------------------------
% (25873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25873)Termination reason: Refutation not found, incomplete strategy

% (25873)Memory used [KB]: 10618
% (25873)Time elapsed: 0.140 s
% (25873)------------------------------
% (25873)------------------------------
fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f60,f37])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f239,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(k1_tarski(X31))
      | sK2 != X30
      | X30 != X31 ) ),
    inference(resolution,[],[f180,f61])).

fof(f180,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,X4)
      | X2 != X3
      | sK2 != X2
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f175,f97])).

fof(f175,plain,(
    ! [X22] :
      ( ~ v1_relat_1(k1_tarski(X22))
      | sK2 != X22 ) ),
    inference(resolution,[],[f152,f61])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK2 != X0
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f97,f75])).

fof(f75,plain,(
    ~ v1_relat_1(k1_tarski(sK2)) ),
    inference(resolution,[],[f72,f61])).

fof(f72,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( sK2 != sK2
      | ~ r2_hidden(sK2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f36,f40])).

fof(f36,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19])).

% (25866)Refutation not found, incomplete strategy% (25866)------------------------------
% (25866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25866)Termination reason: Refutation not found, incomplete strategy

% (25866)Memory used [KB]: 1663
% (25866)Time elapsed: 0.142 s
% (25866)------------------------------
% (25866)------------------------------
% (25876)Refutation not found, incomplete strategy% (25876)------------------------------
% (25876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25876)Termination reason: Refutation not found, incomplete strategy

% (25876)Memory used [KB]: 6140
% (25876)Time elapsed: 0.120 s
% (25876)------------------------------
% (25876)------------------------------
% (25867)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (25867)Refutation not found, incomplete strategy% (25867)------------------------------
% (25867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25867)Termination reason: Refutation not found, incomplete strategy

% (25867)Memory used [KB]: 1663
% (25867)Time elapsed: 0.149 s
% (25867)------------------------------
% (25867)------------------------------
fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f427,plain,(
    ! [X0] :
      ( sK2 != X0
      | v1_relat_1(k1_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f418])).

fof(f418,plain,(
    ! [X0] :
      ( sK2 != X0
      | v1_relat_1(k1_tarski(X0))
      | v1_relat_1(k1_tarski(X0)) ) ),
    inference(superposition,[],[f407,f85])).

fof(f407,plain,(
    ! [X0] :
      ( sK2 != sK3(X0)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f392,f61])).

fof(f392,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X23,k1_tarski(sK2))
      | sK3(X22) != X23
      | v1_relat_1(X22) ) ),
    inference(subsumption_resolution,[],[f391,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f391,plain,(
    ! [X23,X22] :
      ( k1_xboole_0 = sK1
      | sK3(X22) != X23
      | ~ r2_hidden(X23,k1_tarski(sK2))
      | v1_relat_1(X22) ) ),
    inference(subsumption_resolution,[],[f390,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f390,plain,(
    ! [X23,X22] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | sK3(X22) != X23
      | ~ r2_hidden(X23,k1_tarski(sK2))
      | v1_relat_1(X22) ) ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,(
    ! [X23,X22] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | sK3(X22) != X23
      | ~ r2_hidden(X23,k1_tarski(sK2))
      | v1_relat_1(X22) ) ),
    inference(superposition,[],[f42,f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
      | sK3(X1) != X0
      | ~ r2_hidden(X0,k1_tarski(sK2))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f124,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X1,k1_tarski(X2))
      | sK3(X0) != X1
      | k1_xboole_0 = k2_zfmisc_1(X3,X4)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f86,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X3)
      | ~ r2_hidden(X0,X4)
      | sK3(X3) != X0 ) ),
    inference(superposition,[],[f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:53:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (25851)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.49  % (25874)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.50  % (25856)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (25872)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (25850)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (25850)Refutation not found, incomplete strategy% (25850)------------------------------
% 0.20/0.51  % (25850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25850)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25850)Memory used [KB]: 1663
% 0.20/0.51  % (25850)Time elapsed: 0.100 s
% 0.20/0.51  % (25850)------------------------------
% 0.20/0.51  % (25850)------------------------------
% 0.20/0.51  % (25853)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (25852)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (25865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (25864)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (25863)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (25863)Refutation not found, incomplete strategy% (25863)------------------------------
% 0.20/0.51  % (25863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25865)Refutation not found, incomplete strategy% (25865)------------------------------
% 0.20/0.51  % (25865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25863)Memory used [KB]: 1663
% 0.20/0.51  % (25863)Time elapsed: 0.087 s
% 0.20/0.51  % (25863)------------------------------
% 0.20/0.51  % (25863)------------------------------
% 0.20/0.51  % (25865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25865)Memory used [KB]: 10618
% 0.20/0.51  % (25865)Time elapsed: 0.117 s
% 0.20/0.51  % (25865)------------------------------
% 0.20/0.51  % (25865)------------------------------
% 0.20/0.51  % (25858)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (25873)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.52  % (25871)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (25861)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (25861)Refutation not found, incomplete strategy% (25861)------------------------------
% 0.20/0.52  % (25861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25861)Memory used [KB]: 10618
% 0.20/0.52  % (25861)Time elapsed: 0.134 s
% 0.20/0.52  % (25861)------------------------------
% 0.20/0.52  % (25861)------------------------------
% 0.20/0.53  % (25870)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (25877)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (25858)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (25877)Refutation not found, incomplete strategy% (25877)------------------------------
% 0.20/0.53  % (25877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25877)Memory used [KB]: 10746
% 0.20/0.53  % (25877)Time elapsed: 0.129 s
% 0.20/0.53  % (25877)------------------------------
% 0.20/0.53  % (25877)------------------------------
% 0.20/0.53  % (25876)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f432,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(equality_resolution,[],[f428])).
% 0.20/0.53  fof(f428,plain,(
% 0.20/0.53    ( ! [X0] : (sK2 != X0) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f427,f315])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    ( ! [X39,X38,X40] : (~v1_relat_1(k1_tarski(X40)) | X39 != X40 | sK2 != X38 | X38 != X39) )),
% 0.20/0.53    inference(resolution,[],[f261,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.20/0.53    inference(superposition,[],[f59,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    ( ! [X6,X4,X5,X3] : (~r2_hidden(X5,X6) | X3 != X4 | X4 != X5 | sK2 != X3 | ~v1_relat_1(X6)) )),
% 0.20/0.53    inference(resolution,[],[f239,f97])).
% 0.20/0.53  % (25860)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (25854)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (25855)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (25866)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(k1_tarski(X1)) | X0 != X1 | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(superposition,[],[f90,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | v1_relat_1(k1_tarski(X0))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | v1_relat_1(k1_tarski(X0)) | v1_relat_1(k1_tarski(X0))) )),
% 0.20/0.54    inference(superposition,[],[f39,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | v1_relat_1(k1_tarski(X1))) )),
% 0.20/0.54    inference(resolution,[],[f69,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f22])).
% 0.20/0.54  % (25873)Refutation not found, incomplete strategy% (25873)------------------------------
% 0.20/0.54  % (25873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25873)Memory used [KB]: 10618
% 0.20/0.54  % (25873)Time elapsed: 0.140 s
% 0.20/0.54  % (25873)------------------------------
% 0.20/0.54  % (25873)------------------------------
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.20/0.54    inference(superposition,[],[f60,f37])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.20/0.54    inference(equality_resolution,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    ( ! [X30,X31] : (~v1_relat_1(k1_tarski(X31)) | sK2 != X30 | X30 != X31) )),
% 0.20/0.54    inference(resolution,[],[f180,f61])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    ( ! [X4,X2,X3] : (~r2_hidden(X3,X4) | X2 != X3 | sK2 != X2 | ~v1_relat_1(X4)) )),
% 0.20/0.54    inference(resolution,[],[f175,f97])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    ( ! [X22] : (~v1_relat_1(k1_tarski(X22)) | sK2 != X22) )),
% 0.20/0.54    inference(resolution,[],[f152,f61])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sK2 != X0 | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(resolution,[],[f97,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ~v1_relat_1(k1_tarski(sK2))),
% 0.20/0.54    inference(resolution,[],[f72,f61])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (sK2 != sK2 | ~r2_hidden(sK2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f36,f40])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f20,f19])).
% 0.20/0.54  % (25866)Refutation not found, incomplete strategy% (25866)------------------------------
% 0.20/0.54  % (25866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25866)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25866)Memory used [KB]: 1663
% 0.20/0.54  % (25866)Time elapsed: 0.142 s
% 0.20/0.54  % (25866)------------------------------
% 0.20/0.54  % (25866)------------------------------
% 0.20/0.54  % (25876)Refutation not found, incomplete strategy% (25876)------------------------------
% 0.20/0.54  % (25876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25876)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25876)Memory used [KB]: 6140
% 0.20/0.54  % (25876)Time elapsed: 0.120 s
% 0.20/0.54  % (25876)------------------------------
% 0.20/0.54  % (25876)------------------------------
% 0.20/0.55  % (25867)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (25867)Refutation not found, incomplete strategy% (25867)------------------------------
% 0.20/0.55  % (25867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25867)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25867)Memory used [KB]: 1663
% 0.20/0.55  % (25867)Time elapsed: 0.149 s
% 0.20/0.55  % (25867)------------------------------
% 0.20/0.55  % (25867)------------------------------
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => (sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    inference(negated_conjecture,[],[f8])).
% 0.20/0.55  fof(f8,conjecture,(
% 0.20/0.55    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.20/0.55  fof(f427,plain,(
% 0.20/0.55    ( ! [X0] : (sK2 != X0 | v1_relat_1(k1_tarski(X0))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f418])).
% 0.20/0.55  fof(f418,plain,(
% 0.20/0.55    ( ! [X0] : (sK2 != X0 | v1_relat_1(k1_tarski(X0)) | v1_relat_1(k1_tarski(X0))) )),
% 0.20/0.55    inference(superposition,[],[f407,f85])).
% 0.20/0.55  fof(f407,plain,(
% 0.20/0.55    ( ! [X0] : (sK2 != sK3(X0) | v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f392,f61])).
% 0.20/0.55  fof(f392,plain,(
% 0.20/0.55    ( ! [X23,X22] : (~r2_hidden(X23,k1_tarski(sK2)) | sK3(X22) != X23 | v1_relat_1(X22)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f391,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f391,plain,(
% 0.20/0.55    ( ! [X23,X22] : (k1_xboole_0 = sK1 | sK3(X22) != X23 | ~r2_hidden(X23,k1_tarski(sK2)) | v1_relat_1(X22)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f390,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f390,plain,(
% 0.20/0.55    ( ! [X23,X22] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK3(X22) != X23 | ~r2_hidden(X23,k1_tarski(sK2)) | v1_relat_1(X22)) )),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f389])).
% 0.20/0.55  fof(f389,plain,(
% 0.20/0.55    ( ! [X23,X22] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | sK3(X22) != X23 | ~r2_hidden(X23,k1_tarski(sK2)) | v1_relat_1(X22)) )),
% 0.20/0.55    inference(superposition,[],[f42,f263])).
% 0.20/0.55  fof(f263,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK3(X1) != X0 | ~r2_hidden(X0,k1_tarski(sK2)) | v1_relat_1(X1)) )),
% 0.20/0.55    inference(resolution,[],[f124,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X3,X4)) | ~r2_hidden(X1,k1_tarski(X2)) | sK3(X0) != X1 | k1_xboole_0 = k2_zfmisc_1(X3,X4) | v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f86,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.55    inference(flattening,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X3) | ~r2_hidden(X0,X4) | sK3(X3) != X0) )),
% 0.20/0.55    inference(superposition,[],[f39,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (25858)------------------------------
% 0.20/0.55  % (25858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25858)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (25858)Memory used [KB]: 1918
% 0.20/0.55  % (25858)Time elapsed: 0.134 s
% 0.20/0.55  % (25858)------------------------------
% 0.20/0.55  % (25858)------------------------------
% 0.20/0.55  % (25848)Success in time 0.187 s
%------------------------------------------------------------------------------

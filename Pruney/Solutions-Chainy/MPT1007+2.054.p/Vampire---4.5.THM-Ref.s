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
% DateTime   : Thu Dec  3 13:03:59 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 345 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  301 (1029 expanded)
%              Number of equality atoms :   89 ( 296 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20221)Refutation not found, incomplete strategy% (20221)------------------------------
% (20221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20221)Termination reason: Refutation not found, incomplete strategy

% (20221)Memory used [KB]: 1663
% (20221)Time elapsed: 0.180 s
% (20221)------------------------------
% (20221)------------------------------
% (20213)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (20219)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (20208)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (20202)Refutation not found, incomplete strategy% (20202)------------------------------
% (20202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20220)Refutation not found, incomplete strategy% (20220)------------------------------
% (20220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20220)Termination reason: Refutation not found, incomplete strategy

% (20220)Memory used [KB]: 11129
% (20220)Time elapsed: 0.167 s
% (20220)------------------------------
% (20220)------------------------------
fof(f305,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f193,f286,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

% (20202)Termination reason: Refutation not found, incomplete strategy

% (20202)Memory used [KB]: 11129
fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f18])).

% (20202)Time elapsed: 0.185 s
fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f286,plain,(
    ! [X4] : ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f273,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f273,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(X4,sK6(k1_xboole_0,X4)))
      | ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f214,f231])).

fof(f231,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f230,f141])).

fof(f141,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f124,f140,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f140,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f124,f57,f61,f125,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f125,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f94,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f59,f93])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f42])).

% (20202)------------------------------
% (20202)------------------------------
fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f61,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f94,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f230,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f139,f217])).

fof(f217,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f139,f169])).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | sK0 = X2 ) ),
    inference(resolution,[],[f135,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f135,plain,(
    ! [X3] :
      ( r2_hidden(X3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f94,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK3(sK2),sK4(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f214,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r1_tarski(sK2,k4_tarski(X4,sK6(sK2,X4))) ) ),
    inference(resolution,[],[f136,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f136,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,sK6(sK2,X1)),sK2)
      | ~ r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(subsumption_resolution,[],[f133,f126])).

fof(f126,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f60,f95,f94,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f95,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f58,f93])).

fof(f58,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0))
      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
      | r2_hidden(k4_tarski(X1,sK6(sK2,X1)),sK2) ) ),
    inference(resolution,[],[f94,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK7(X1,X2),X6),X2)
            & r2_hidden(sK7(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f51,f53,f52])).

fof(f52,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK7(X1,X2),X6),X2)
        & r2_hidden(sK7(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f193,plain,(
    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f146,f64])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f146,plain,(
    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f144,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f93])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f144,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f63,f140,f69])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:13:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (20195)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.57  % (20206)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (20198)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (20212)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.58  % (20214)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (20203)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.58  % (20204)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (20202)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.59  % (20220)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.59  % (20215)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (20207)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.60  % (20194)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.78/0.60  % (20192)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.60  % (20196)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.78/0.60  % (20206)Refutation not found, incomplete strategy% (20206)------------------------------
% 1.78/0.60  % (20206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (20206)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (20206)Memory used [KB]: 1791
% 1.78/0.60  % (20206)Time elapsed: 0.150 s
% 1.78/0.60  % (20206)------------------------------
% 1.78/0.60  % (20206)------------------------------
% 1.78/0.60  % (20197)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.78/0.60  % (20199)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.61  % (20193)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.78/0.61  % (20221)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.78/0.61  % (20203)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  % (20221)Refutation not found, incomplete strategy% (20221)------------------------------
% 1.78/0.61  % (20221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (20221)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (20221)Memory used [KB]: 1663
% 1.78/0.61  % (20221)Time elapsed: 0.180 s
% 1.78/0.61  % (20221)------------------------------
% 1.78/0.61  % (20221)------------------------------
% 1.78/0.62  % (20213)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.78/0.62  % (20219)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.97/0.62  % (20208)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.97/0.63  % (20202)Refutation not found, incomplete strategy% (20202)------------------------------
% 1.97/0.63  % (20202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (20220)Refutation not found, incomplete strategy% (20220)------------------------------
% 1.97/0.63  % (20220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (20220)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (20220)Memory used [KB]: 11129
% 1.97/0.63  % (20220)Time elapsed: 0.167 s
% 1.97/0.63  % (20220)------------------------------
% 1.97/0.63  % (20220)------------------------------
% 1.97/0.63  fof(f305,plain,(
% 1.97/0.63    $false),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f193,f286,f67])).
% 1.97/0.63  fof(f67,plain,(
% 1.97/0.63    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f47])).
% 1.97/0.63  % (20202)Termination reason: Refutation not found, incomplete strategy
% 1.97/0.63  
% 1.97/0.63  % (20202)Memory used [KB]: 11129
% 1.97/0.63  fof(f47,plain,(
% 1.97/0.63    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f46])).
% 1.97/0.63  fof(f46,plain,(
% 1.97/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f28,plain,(
% 1.97/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.97/0.63    inference(ennf_transformation,[],[f22])).
% 1.97/0.63  fof(f22,plain,(
% 1.97/0.63    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.97/0.63    inference(pure_predicate_removal,[],[f18])).
% 1.97/0.63  % (20202)Time elapsed: 0.185 s
% 1.97/0.63  fof(f18,axiom,(
% 1.97/0.63    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.97/0.63  fof(f286,plain,(
% 1.97/0.63    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f273,f62])).
% 1.97/0.63  fof(f62,plain,(
% 1.97/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f1])).
% 1.97/0.63  fof(f1,axiom,(
% 1.97/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.97/0.63  fof(f273,plain,(
% 1.97/0.63    ( ! [X4] : (~r1_tarski(k1_xboole_0,k4_tarski(X4,sK6(k1_xboole_0,X4))) | ~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.97/0.63    inference(backward_demodulation,[],[f214,f231])).
% 1.97/0.63  fof(f231,plain,(
% 1.97/0.63    k1_xboole_0 = sK2),
% 1.97/0.63    inference(subsumption_resolution,[],[f230,f141])).
% 1.97/0.63  fof(f141,plain,(
% 1.97/0.63    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2)) )),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f124,f140,f75])).
% 1.97/0.63  fof(f75,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f34])).
% 1.97/0.63  fof(f34,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.97/0.63    inference(flattening,[],[f33])).
% 1.97/0.63  fof(f33,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.97/0.63    inference(ennf_transformation,[],[f11])).
% 1.97/0.63  fof(f11,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.97/0.63  fof(f140,plain,(
% 1.97/0.63    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f124,f57,f61,f125,f70])).
% 1.97/0.63  fof(f70,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f31])).
% 1.97/0.63  fof(f31,plain,(
% 1.97/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.97/0.63    inference(flattening,[],[f30])).
% 1.97/0.63  fof(f30,plain,(
% 1.97/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.97/0.63    inference(ennf_transformation,[],[f13])).
% 1.97/0.63  fof(f13,axiom,(
% 1.97/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.97/0.63  fof(f125,plain,(
% 1.97/0.63    v5_relat_1(sK2,sK1)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f94,f78])).
% 1.97/0.63  fof(f78,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f36])).
% 1.97/0.63  fof(f36,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f23])).
% 1.97/0.63  fof(f23,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.97/0.63    inference(pure_predicate_removal,[],[f16])).
% 1.97/0.63  fof(f16,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.97/0.63  fof(f94,plain,(
% 1.97/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.97/0.63    inference(definition_unfolding,[],[f59,f93])).
% 1.97/0.63  fof(f93,plain,(
% 1.97/0.63    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.97/0.63    inference(definition_unfolding,[],[f65,f92])).
% 1.97/0.63  fof(f92,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.97/0.63    inference(definition_unfolding,[],[f68,f74])).
% 1.97/0.63  fof(f74,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f5])).
% 1.97/0.63  fof(f5,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.97/0.63  fof(f68,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f4])).
% 1.97/0.63  fof(f4,axiom,(
% 1.97/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.97/0.63  fof(f65,plain,(
% 1.97/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f3])).
% 1.97/0.63  fof(f3,axiom,(
% 1.97/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.97/0.63  fof(f59,plain,(
% 1.97/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f43,plain,(
% 1.97/0.63    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f42])).
% 1.97/0.63  % (20202)------------------------------
% 1.97/0.63  % (20202)------------------------------
% 1.97/0.63  fof(f42,plain,(
% 1.97/0.63    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f25,plain,(
% 1.97/0.63    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.97/0.63    inference(flattening,[],[f24])).
% 1.97/0.63  fof(f24,plain,(
% 1.97/0.63    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.97/0.63    inference(ennf_transformation,[],[f21])).
% 1.97/0.63  fof(f21,negated_conjecture,(
% 1.97/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.97/0.63    inference(negated_conjecture,[],[f20])).
% 1.97/0.63  fof(f20,conjecture,(
% 1.97/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.97/0.63  fof(f61,plain,(
% 1.97/0.63    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f57,plain,(
% 1.97/0.63    v1_funct_1(sK2)),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f124,plain,(
% 1.97/0.63    v1_relat_1(sK2)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f94,f77])).
% 1.97/0.63  fof(f77,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f35])).
% 1.97/0.63  fof(f35,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f15])).
% 1.97/0.63  fof(f15,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.97/0.63  fof(f230,plain,(
% 1.97/0.63    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.97/0.63    inference(duplicate_literal_removal,[],[f229])).
% 1.97/0.63  fof(f229,plain,(
% 1.97/0.63    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.97/0.63    inference(superposition,[],[f139,f217])).
% 1.97/0.63  fof(f217,plain,(
% 1.97/0.63    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.97/0.63    inference(resolution,[],[f139,f169])).
% 1.97/0.63  fof(f169,plain,(
% 1.97/0.63    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | sK0 = X2) )),
% 1.97/0.63    inference(resolution,[],[f135,f100])).
% 1.97/0.63  fof(f100,plain,(
% 1.97/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 1.97/0.63    inference(definition_unfolding,[],[f89,f93])).
% 1.97/0.63  fof(f89,plain,(
% 1.97/0.63    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f56])).
% 1.97/0.63  fof(f56,plain,(
% 1.97/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.97/0.63    inference(flattening,[],[f55])).
% 1.97/0.63  fof(f55,plain,(
% 1.97/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.97/0.63    inference(nnf_transformation,[],[f7])).
% 1.97/0.63  fof(f7,axiom,(
% 1.97/0.63    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.97/0.63  fof(f135,plain,(
% 1.97/0.63    ( ! [X3] : (r2_hidden(X3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X3,sK2)) )),
% 1.97/0.63    inference(resolution,[],[f94,f69])).
% 1.97/0.63  fof(f69,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f29])).
% 1.97/0.63  fof(f29,plain,(
% 1.97/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.63    inference(ennf_transformation,[],[f8])).
% 1.97/0.63  fof(f8,axiom,(
% 1.97/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.97/0.63  fof(f139,plain,(
% 1.97/0.63    r2_hidden(k4_tarski(sK3(sK2),sK4(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.97/0.63    inference(resolution,[],[f124,f66])).
% 1.97/0.63  fof(f66,plain,(
% 1.97/0.63    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | k1_xboole_0 = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f45])).
% 1.97/0.63  fof(f45,plain,(
% 1.97/0.63    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | ~v1_relat_1(X0))),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f44])).
% 1.97/0.63  fof(f44,plain,(
% 1.97/0.63    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f27,plain,(
% 1.97/0.63    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.97/0.63    inference(flattening,[],[f26])).
% 1.97/0.63  fof(f26,plain,(
% 1.97/0.63    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.97/0.63    inference(ennf_transformation,[],[f12])).
% 1.97/0.63  fof(f12,axiom,(
% 1.97/0.63    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.97/0.63  fof(f214,plain,(
% 1.97/0.63    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(sK2,k4_tarski(X4,sK6(sK2,X4)))) )),
% 1.97/0.63    inference(resolution,[],[f136,f73])).
% 1.97/0.63  fof(f73,plain,(
% 1.97/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f32])).
% 1.97/0.63  fof(f32,plain,(
% 1.97/0.63    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.97/0.63    inference(ennf_transformation,[],[f14])).
% 1.97/0.63  fof(f14,axiom,(
% 1.97/0.63    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.97/0.63  fof(f136,plain,(
% 1.97/0.63    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK6(sK2,X1)),sK2) | ~r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.97/0.63    inference(subsumption_resolution,[],[f133,f126])).
% 1.97/0.63  fof(f126,plain,(
% 1.97/0.63    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f60,f95,f94,f79])).
% 1.97/0.63  fof(f79,plain,(
% 1.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f49])).
% 1.97/0.63  fof(f49,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(nnf_transformation,[],[f38])).
% 1.97/0.63  fof(f38,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(flattening,[],[f37])).
% 1.97/0.63  fof(f37,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.97/0.63    inference(ennf_transformation,[],[f19])).
% 1.97/0.63  fof(f19,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.97/0.63  fof(f95,plain,(
% 1.97/0.63    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.97/0.63    inference(definition_unfolding,[],[f58,f93])).
% 1.97/0.63  fof(f58,plain,(
% 1.97/0.63    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f60,plain,(
% 1.97/0.63    k1_xboole_0 != sK1),
% 1.97/0.63    inference(cnf_transformation,[],[f43])).
% 1.97/0.63  fof(f133,plain,(
% 1.97/0.63    ( ! [X1] : (~r2_hidden(X1,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | r2_hidden(k4_tarski(X1,sK6(sK2,X1)),sK2)) )),
% 1.97/0.63    inference(resolution,[],[f94,f87])).
% 1.97/0.63  fof(f87,plain,(
% 1.97/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f54])).
% 1.97/0.63  fof(f54,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK7(X1,X2),X6),X2) & r2_hidden(sK7(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f51,f53,f52])).
% 1.97/0.63  fof(f52,plain,(
% 1.97/0.63    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f53,plain,(
% 1.97/0.63    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK7(X1,X2),X6),X2) & r2_hidden(sK7(X1,X2),X1)))),
% 1.97/0.63    introduced(choice_axiom,[])).
% 1.97/0.63  fof(f51,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.97/0.63    inference(rectify,[],[f50])).
% 1.97/0.63  fof(f50,plain,(
% 1.97/0.63    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.97/0.63    inference(nnf_transformation,[],[f39])).
% 1.97/0.63  fof(f39,plain,(
% 1.97/0.63    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.97/0.63    inference(ennf_transformation,[],[f17])).
% 1.97/0.63  fof(f17,axiom,(
% 1.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.97/0.63  fof(f193,plain,(
% 1.97/0.63    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.97/0.63    inference(superposition,[],[f146,f64])).
% 1.97/0.63  fof(f64,plain,(
% 1.97/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.97/0.63    inference(cnf_transformation,[],[f2])).
% 1.97/0.63  fof(f2,axiom,(
% 1.97/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.97/0.63  fof(f146,plain,(
% 1.97/0.63    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f144,f97])).
% 1.97/0.63  fof(f97,plain,(
% 1.97/0.63    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.97/0.63    inference(definition_unfolding,[],[f71,f93])).
% 1.97/0.63  fof(f71,plain,(
% 1.97/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.97/0.63    inference(cnf_transformation,[],[f48])).
% 1.97/0.63  fof(f48,plain,(
% 1.97/0.63    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.97/0.63    inference(nnf_transformation,[],[f6])).
% 1.97/0.63  fof(f6,axiom,(
% 1.97/0.63    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.97/0.63  fof(f144,plain,(
% 1.97/0.63    ~r2_hidden(sK0,k1_xboole_0)),
% 1.97/0.63    inference(unit_resulting_resolution,[],[f63,f140,f69])).
% 1.97/0.63  fof(f63,plain,(
% 1.97/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.97/0.63    inference(cnf_transformation,[],[f9])).
% 1.97/0.63  fof(f9,axiom,(
% 1.97/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.97/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.97/0.63  % SZS output end Proof for theBenchmark
% 1.97/0.63  % (20203)------------------------------
% 1.97/0.63  % (20203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.63  % (20203)Termination reason: Refutation
% 1.97/0.63  
% 1.97/0.63  % (20203)Memory used [KB]: 6524
% 1.97/0.63  % (20203)Time elapsed: 0.183 s
% 1.97/0.63  % (20203)------------------------------
% 1.97/0.63  % (20203)------------------------------
% 1.97/0.63  % (20191)Success in time 0.266 s
%------------------------------------------------------------------------------

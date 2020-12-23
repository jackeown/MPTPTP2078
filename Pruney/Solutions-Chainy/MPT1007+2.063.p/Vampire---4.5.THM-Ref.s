%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 271 expanded)
%              Number of leaves         :   12 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  251 (1202 expanded)
%              Number of equality atoms :   48 ( 250 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f56])).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f161,plain,(
    v1_xboole_0(k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f159,f97])).

fof(f97,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f94,f35])).

fof(f35,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).

fof(f24,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f32,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f90,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f159,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | v1_xboole_0(k1_tarski(sK0)) ),
    inference(superposition,[],[f58,f154])).

fof(f154,plain,(
    sK0 = sK3(k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f153,f56])).

fof(f153,plain,
    ( sK0 = sK3(k1_tarski(sK0))
    | v1_xboole_0(k1_tarski(sK0)) ),
    inference(resolution,[],[f134,f58])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f131,f109])).

fof(f109,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(resolution,[],[f104,f69])).

fof(f69,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f68,f59])).

fof(f59,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f68,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f35,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (23086)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f104,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK1)
      | ~ r2_hidden(X6,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f76,f59])).

fof(f76,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),sK1) ) ),
    inference(subsumption_resolution,[],[f72,f31])).

fof(f72,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | r2_hidden(k1_funct_1(sK2,X6),sK1) ) ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK2)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (23085)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_xboole_0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f100,f79])).

fof(f79,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f78,f59])).

fof(f78,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(subsumption_resolution,[],[f73,f31])).

fof(f73,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | sK0 = X7 ) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | sK0 = X0 ) ),
    inference(resolution,[],[f49,f61])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_xboole_0,sK1) ) ),
    inference(subsumption_resolution,[],[f99,f59])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f98,f31])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f94,f52])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (23090)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (23094)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (23094)Refutation not found, incomplete strategy% (23094)------------------------------
% 0.21/0.53  % (23094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23094)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23094)Memory used [KB]: 10618
% 0.21/0.53  % (23094)Time elapsed: 0.116 s
% 0.21/0.53  % (23094)------------------------------
% 0.21/0.53  % (23094)------------------------------
% 0.21/0.54  % (23102)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (23081)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (23100)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (23092)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (23084)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (23087)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (23097)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.58  % (23092)Refutation not found, incomplete strategy% (23092)------------------------------
% 0.21/0.58  % (23092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (23092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (23092)Memory used [KB]: 1791
% 0.21/0.58  % (23092)Time elapsed: 0.104 s
% 0.21/0.58  % (23092)------------------------------
% 0.21/0.58  % (23092)------------------------------
% 0.21/0.58  % (23087)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % (23082)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.59  % (23083)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f162,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f161,f56])).
% 0.21/0.59  fof(f56,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.59    inference(superposition,[],[f42,f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.59  fof(f42,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f4])).
% 0.21/0.59  fof(f4,axiom,(
% 0.21/0.59    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.21/0.59  fof(f161,plain,(
% 0.21/0.59    v1_xboole_0(k1_tarski(sK0))),
% 0.21/0.59    inference(subsumption_resolution,[],[f159,f97])).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.21/0.59    inference(resolution,[],[f94,f35])).
% 0.21/0.59  fof(f35,plain,(
% 0.21/0.59    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f25,plain,(
% 0.21/0.59    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f15,plain,(
% 0.21/0.59    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.59    inference(flattening,[],[f14])).
% 0.21/0.59  fof(f14,plain,(
% 0.21/0.59    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.59    inference(negated_conjecture,[],[f12])).
% 0.21/0.59  fof(f12,conjecture,(
% 0.21/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f93,f31])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    v1_funct_1(sK2)),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f93,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f92,f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f90,f34])).
% 0.21/0.59  fof(f34,plain,(
% 0.21/0.59    k1_xboole_0 != sK1),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f90,plain,(
% 0.21/0.59    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)) )),
% 0.21/0.59    inference(resolution,[],[f48,f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.59    inference(cnf_transformation,[],[f25])).
% 0.21/0.59  fof(f48,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.59    inference(flattening,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.59  fof(f159,plain,(
% 0.21/0.59    r2_hidden(sK0,k1_tarski(sK0)) | v1_xboole_0(k1_tarski(sK0))),
% 0.21/0.59    inference(superposition,[],[f58,f154])).
% 0.21/0.59  fof(f154,plain,(
% 0.21/0.59    sK0 = sK3(k1_tarski(sK0))),
% 0.21/0.59    inference(subsumption_resolution,[],[f153,f56])).
% 0.21/0.59  fof(f153,plain,(
% 0.21/0.59    sK0 = sK3(k1_tarski(sK0)) | v1_xboole_0(k1_tarski(sK0))),
% 0.21/0.59    inference(resolution,[],[f134,f58])).
% 0.21/0.59  fof(f134,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | sK0 = X0) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f131,f109])).
% 0.21/0.59  fof(f109,plain,(
% 0.21/0.59    ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.59    inference(resolution,[],[f104,f69])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_xboole_0,sK1)),
% 0.21/0.59    inference(subsumption_resolution,[],[f68,f59])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    v1_relat_1(sK2)),
% 0.21/0.59    inference(resolution,[],[f47,f33])).
% 0.21/0.59  fof(f47,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.59    inference(ennf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.59  fof(f68,plain,(
% 0.21/0.59    ~r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.59    inference(subsumption_resolution,[],[f67,f31])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    ~r2_hidden(k1_xboole_0,sK1) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.59    inference(superposition,[],[f35,f52])).
% 0.21/0.59  fof(f52,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f40])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(flattening,[],[f16])).
% 0.21/0.59  fof(f16,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  % (23086)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.59  fof(f104,plain,(
% 0.21/0.59    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.59    inference(resolution,[],[f77,f35])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    ( ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK1) | ~r2_hidden(X6,k1_relat_1(sK2))) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f76,f59])).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),sK1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f72,f31])).
% 0.21/0.59  fof(f72,plain,(
% 0.21/0.59    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k1_funct_1(sK2,X6),sK1)) )),
% 0.21/0.59    inference(resolution,[],[f54,f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(X0,sK1)) )),
% 0.21/0.59    inference(resolution,[],[f50,f61])).
% 0.21/0.59  fof(f61,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.59    inference(resolution,[],[f45,f33])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.59    inference(flattening,[],[f29])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.21/0.59    inference(nnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.21/0.59  fof(f54,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(equality_resolution,[],[f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f26])).
% 0.21/0.59  % (23085)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  fof(f131,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_xboole_0,sK1) | sK0 = X0) )),
% 0.21/0.59    inference(resolution,[],[f100,f79])).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | sK0 = X7) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f78,f59])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f73,f31])).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    ( ! [X7] : (~r2_hidden(X7,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 = X7) )),
% 0.21/0.59    inference(resolution,[],[f54,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) )),
% 0.21/0.59    inference(resolution,[],[f49,f61])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | X0 = X2) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.59  fof(f100,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_xboole_0,sK1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f99,f59])).
% 0.21/0.59  fof(f99,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f98,f31])).
% 0.21/0.59  fof(f98,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.59    inference(superposition,[],[f94,f52])).
% 0.21/0.59  fof(f58,plain,(
% 0.21/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.59    inference(resolution,[],[f44,f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(flattening,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (23087)------------------------------
% 0.21/0.59  % (23087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (23087)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (23087)Memory used [KB]: 1791
% 0.21/0.59  % (23087)Time elapsed: 0.167 s
% 0.21/0.59  % (23087)------------------------------
% 0.21/0.59  % (23087)------------------------------
% 0.21/0.60  % (23077)Success in time 0.237 s
%------------------------------------------------------------------------------

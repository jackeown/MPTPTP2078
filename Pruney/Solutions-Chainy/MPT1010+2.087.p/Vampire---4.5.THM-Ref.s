%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 (1449 expanded)
%              Number of leaves         :   14 ( 338 expanded)
%              Depth                    :   24
%              Number of atoms          :  339 (6543 expanded)
%              Number of equality atoms :  144 (2251 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(subsumption_resolution,[],[f614,f464])).

fof(f464,plain,(
    ! [X3] : r2_hidden(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f93,f458])).

fof(f458,plain,(
    ! [X0] : k1_xboole_0 = X0 ),
    inference(subsumption_resolution,[],[f442,f96])).

fof(f96,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

% (26010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (25998)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (26006)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (26003)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (26002)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (26004)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (25995)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (25996)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (26010)Refutation not found, incomplete strategy% (26010)------------------------------
% (26010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f442,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f61,f382])).

fof(f382,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f381,f54])).

fof(f54,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f381,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f377,f185])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f183,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f183,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f182,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f182,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f178,f52])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f377,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f370])).

fof(f370,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f369,f129])).

fof(f129,plain,(
    v5_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f369,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,k1_tarski(X0))
      | sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f368,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f368,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ r2_hidden(sK2,k1_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f354,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f122,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f122,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f57,f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f354,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f55,f237])).

fof(f237,plain,(
    ! [X6,X7,X5] :
      ( k1_funct_1(X5,X7) = X6
      | ~ v5_relat_1(X5,k1_tarski(X6))
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(X7,k1_relat_1(X5))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f235,f112])).

fof(f112,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(resolution,[],[f58,f93])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f235,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ v5_relat_1(X5,k1_tarski(X6))
      | ~ v1_relat_1(X5)
      | v1_xboole_0(k1_tarski(X6))
      | ~ r2_hidden(X7,k1_relat_1(X5))
      | k1_funct_1(X5,X7) = X6 ) ),
    inference(resolution,[],[f168,f94])).

fof(f94,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f168,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(k1_funct_1(X13,X12),X14)
      | ~ v1_funct_1(X13)
      | ~ v5_relat_1(X13,X14)
      | ~ v1_relat_1(X13)
      | v1_xboole_0(X14)
      | ~ r2_hidden(X12,k1_relat_1(X13)) ) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f55,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f93,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f614,plain,(
    ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f613,f458])).

fof(f613,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f612,f592])).

fof(f592,plain,(
    v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f591,f464])).

fof(f591,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | v5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f590,f458])).

fof(f590,plain,(
    ! [X1] :
      ( v5_relat_1(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(sK1,k1_tarski(X1)) ) ),
    inference(forward_demodulation,[],[f480,f458])).

fof(f480,plain,(
    ! [X1] :
      ( v5_relat_1(sK3,k1_xboole_0)
      | ~ r2_hidden(sK1,k1_tarski(X1)) ) ),
    inference(backward_demodulation,[],[f222,f458])).

fof(f222,plain,(
    ! [X1] :
      ( v5_relat_1(sK3,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1)) ) ),
    inference(superposition,[],[f129,f204])).

fof(f204,plain,(
    ! [X2,X3] :
      ( k1_tarski(X3) = k1_tarski(X2)
      | ~ r2_hidden(X2,k1_tarski(X3)) ) ),
    inference(subsumption_resolution,[],[f202,f94])).

fof(f202,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(superposition,[],[f70,f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( sK4(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1)
      | X0 != X1 ) ),
    inference(subsumption_resolution,[],[f176,f93])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | sK4(X0,k1_tarski(X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_tarski(X1)
      | sK4(X0,k1_tarski(X1)) = X0 ) ),
    inference(superposition,[],[f70,f139])).

fof(f139,plain,(
    ! [X2,X3] :
      ( sK4(X2,k1_tarski(X3)) = X3
      | k1_tarski(X3) = k1_tarski(X2)
      | sK4(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f612,plain,
    ( ~ v5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f611,f458])).

fof(f611,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f501,f589])).

fof(f589,plain,(
    ! [X0,X3] : X0 = X3 ),
    inference(subsumption_resolution,[],[f465,f464])).

fof(f465,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | X0 = X3 ) ),
    inference(backward_demodulation,[],[f94,f458])).

fof(f501,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,k1_xboole_0)
      | sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(backward_demodulation,[],[f369,f458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (25993)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (25992)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (25985)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (26008)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (26000)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (25989)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (25988)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (25987)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (25994)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (25990)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (26001)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (26005)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (26001)Refutation not found, incomplete strategy% (26001)------------------------------
% 0.21/0.53  % (26001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26007)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (26001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26001)Memory used [KB]: 10746
% 0.21/0.53  % (26001)Time elapsed: 0.117 s
% 0.21/0.53  % (26001)------------------------------
% 0.21/0.53  % (26001)------------------------------
% 0.21/0.53  % (25999)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (25999)Refutation not found, incomplete strategy% (25999)------------------------------
% 0.21/0.53  % (25999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25999)Memory used [KB]: 1791
% 0.21/0.53  % (25999)Time elapsed: 0.081 s
% 0.21/0.53  % (25999)------------------------------
% 0.21/0.53  % (25999)------------------------------
% 0.21/0.53  % (25997)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (25991)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26013)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (26011)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (25986)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (26012)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (26014)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (25986)Refutation not found, incomplete strategy% (25986)------------------------------
% 0.21/0.54  % (25986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25986)Memory used [KB]: 1663
% 0.21/0.54  % (25986)Time elapsed: 0.125 s
% 0.21/0.54  % (25986)------------------------------
% 0.21/0.54  % (25986)------------------------------
% 0.21/0.54  % (26014)Refutation not found, incomplete strategy% (26014)------------------------------
% 0.21/0.54  % (26014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26014)Memory used [KB]: 1663
% 0.21/0.54  % (26014)Time elapsed: 0.127 s
% 0.21/0.54  % (26014)------------------------------
% 0.21/0.54  % (26014)------------------------------
% 0.21/0.55  % (26009)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (26009)Refutation not found, incomplete strategy% (26009)------------------------------
% 0.21/0.55  % (26009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26009)Memory used [KB]: 10746
% 0.21/0.55  % (26009)Time elapsed: 0.111 s
% 0.21/0.55  % (26009)------------------------------
% 0.21/0.55  % (26009)------------------------------
% 0.21/0.55  % (25994)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f615,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f614,f464])).
% 0.21/0.55  fof(f464,plain,(
% 0.21/0.55    ( ! [X3] : (r2_hidden(X3,k1_xboole_0)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f93,f458])).
% 0.21/0.55  fof(f458,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f442,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(flattening,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  % (26010)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (25998)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (26006)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (26003)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (26002)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (26004)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (25995)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (25996)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (26010)Refutation not found, incomplete strategy% (26010)------------------------------
% 0.21/0.56  % (26010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  fof(f442,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(superposition,[],[f61,f382])).
% 0.21/0.56  fof(f382,plain,(
% 0.21/0.56    k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.56    inference(subsumption_resolution,[],[f381,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    r2_hidden(sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f17])).
% 0.21/0.57  fof(f17,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 0.21/0.57  fof(f381,plain,(
% 0.21/0.57    ~r2_hidden(sK2,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.57    inference(superposition,[],[f377,f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f183,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.21/0.57    inference(superposition,[],[f182,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f178,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.21/0.57    inference(resolution,[],[f77,f53])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f377,plain,(
% 0.21/0.57    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f370])).
% 0.21/0.57  fof(f370,plain,(
% 0.21/0.57    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.57    inference(resolution,[],[f369,f129])).
% 0.21/0.57  fof(f129,plain,(
% 0.21/0.57    v5_relat_1(sK3,k1_tarski(sK1))),
% 0.21/0.57    inference(resolution,[],[f76,f53])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.57  fof(f369,plain,(
% 0.21/0.57    ( ! [X0] : (~v5_relat_1(sK3,k1_tarski(X0)) | sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f368,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    v1_funct_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f368,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f354,f123])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    v1_relat_1(sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))),
% 0.21/0.57    inference(resolution,[],[f57,f53])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.57  fof(f354,plain,(
% 0.21/0.57    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3)) )),
% 0.21/0.57    inference(superposition,[],[f55,f237])).
% 0.21/0.57  fof(f237,plain,(
% 0.21/0.57    ( ! [X6,X7,X5] : (k1_funct_1(X5,X7) = X6 | ~v5_relat_1(X5,k1_tarski(X6)) | ~v1_relat_1(X5) | ~r2_hidden(X7,k1_relat_1(X5)) | ~v1_funct_1(X5)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f235,f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.57    inference(resolution,[],[f58,f93])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~v5_relat_1(X5,k1_tarski(X6)) | ~v1_relat_1(X5) | v1_xboole_0(k1_tarski(X6)) | ~r2_hidden(X7,k1_relat_1(X5)) | k1_funct_1(X5,X7) = X6) )),
% 0.21/0.57    inference(resolution,[],[f168,f94])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.57    inference(equality_resolution,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.57    inference(rectify,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    ( ! [X14,X12,X13] : (r2_hidden(k1_funct_1(X13,X12),X14) | ~v1_funct_1(X13) | ~v5_relat_1(X13,X14) | ~v1_relat_1(X13) | v1_xboole_0(X14) | ~r2_hidden(X12,k1_relat_1(X13))) )),
% 0.21/0.57    inference(resolution,[],[f83,f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    sK1 != k1_funct_1(sK3,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.57    inference(equality_resolution,[],[f92])).
% 0.21/0.57  fof(f92,plain,(
% 0.21/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.57    inference(equality_resolution,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f614,plain,(
% 0.21/0.57    ~r2_hidden(sK2,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f613,f458])).
% 0.21/0.57  fof(f613,plain,(
% 0.21/0.57    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.57    inference(subsumption_resolution,[],[f612,f592])).
% 0.21/0.57  fof(f592,plain,(
% 0.21/0.57    v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f591,f464])).
% 0.21/0.57  fof(f591,plain,(
% 0.21/0.57    ~r2_hidden(sK1,k1_xboole_0) | v5_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f590,f458])).
% 0.21/0.57  fof(f590,plain,(
% 0.21/0.57    ( ! [X1] : (v5_relat_1(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK1,k1_tarski(X1))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f480,f458])).
% 0.21/0.57  fof(f480,plain,(
% 0.21/0.57    ( ! [X1] : (v5_relat_1(sK3,k1_xboole_0) | ~r2_hidden(sK1,k1_tarski(X1))) )),
% 0.21/0.57    inference(backward_demodulation,[],[f222,f458])).
% 0.21/0.57  fof(f222,plain,(
% 0.21/0.57    ( ! [X1] : (v5_relat_1(sK3,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1))) )),
% 0.21/0.57    inference(superposition,[],[f129,f204])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    ( ! [X2,X3] : (k1_tarski(X3) = k1_tarski(X2) | ~r2_hidden(X2,k1_tarski(X3))) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f202,f94])).
% 0.21/0.57  fof(f202,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f201])).
% 0.21/0.57  fof(f201,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f199])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.57    inference(superposition,[],[f70,f177])).
% 0.21/0.57  fof(f177,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sK4(X0,k1_tarski(X1)) = X0 | k1_tarski(X0) = k1_tarski(X1) | X0 != X1) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f176,f93])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.57    inference(superposition,[],[f70,f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X2,X3] : (sK4(X2,k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(X2) | sK4(X2,k1_tarski(X3)) = X2) )),
% 0.21/0.57    inference(resolution,[],[f69,f94])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k1_tarski(X0) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f612,plain,(
% 0.21/0.57    ~v5_relat_1(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.57    inference(forward_demodulation,[],[f611,f458])).
% 0.21/0.57  fof(f611,plain,(
% 0.21/0.57    ~v5_relat_1(sK3,k1_xboole_0) | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.57    inference(subsumption_resolution,[],[f501,f589])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    ( ! [X0,X3] : (X0 = X3) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f465,f464])).
% 0.21/0.57  fof(f465,plain,(
% 0.21/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_xboole_0) | X0 = X3) )),
% 0.21/0.57    inference(backward_demodulation,[],[f94,f458])).
% 0.21/0.57  fof(f501,plain,(
% 0.21/0.57    ( ! [X0] : (~v5_relat_1(sK3,k1_xboole_0) | sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 0.21/0.57    inference(backward_demodulation,[],[f369,f458])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (25994)------------------------------
% 0.21/0.57  % (25994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (25994)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (25994)Memory used [KB]: 1918
% 0.21/0.57  % (25994)Time elapsed: 0.140 s
% 0.21/0.57  % (25994)------------------------------
% 0.21/0.57  % (25994)------------------------------
% 0.21/0.57  % (26010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  % (25984)Success in time 0.203 s
%------------------------------------------------------------------------------

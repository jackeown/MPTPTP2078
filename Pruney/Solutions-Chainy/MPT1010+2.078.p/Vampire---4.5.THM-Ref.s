%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:02 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   77 (1706 expanded)
%              Number of leaves         :   10 ( 390 expanded)
%              Depth                    :   19
%              Number of atoms          :  258 (7956 expanded)
%              Number of equality atoms :  114 (2121 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f126])).

fof(f126,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f35,f125])).

fof(f125,plain,(
    k1_xboole_0 = k1_funct_1(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( sK1 != sK1
    | k1_xboole_0 = k1_funct_1(sK3,sK2) ),
    inference(superposition,[],[f35,f115])).

fof(f115,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | k1_xboole_0 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f114,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK3))
      | k1_xboole_0 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f81,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

% (19530)Refutation not found, incomplete strategy% (19530)------------------------------
% (19530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19527)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (19522)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (19542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (19543)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (19520)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (19530)Termination reason: Refutation not found, incomplete strategy

% (19530)Memory used [KB]: 10746
% (19530)Time elapsed: 0.130 s
% (19530)------------------------------
% (19530)------------------------------
% (19518)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (19515)Refutation not found, incomplete strategy% (19515)------------------------------
% (19515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19515)Termination reason: Refutation not found, incomplete strategy

% (19515)Memory used [KB]: 1791
% (19515)Time elapsed: 0.091 s
% (19515)------------------------------
% (19515)------------------------------
fof(f24,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f23])).

fof(f23,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_hidden(X0,k1_relat_1(sK3))
      | k1_xboole_0 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f67,plain,(
    ! [X3] :
      ( ~ v1_relat_1(sK3)
      | k1_xboole_0 = k1_funct_1(sK3,X3)
      | r2_hidden(X3,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f31,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f100,f33])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK3)
      | sK1 = X2 ) ),
    inference(resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1)))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f31,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f244,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f243,f162])).

fof(f162,plain,(
    k1_xboole_0 = k1_funct_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f158,f161])).

fof(f161,plain,(
    ! [X4] : k1_xboole_0 != k4_xboole_0(k1_xboole_0,X4) ),
    inference(subsumption_resolution,[],[f155,f153])).

fof(f153,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
      | r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f47,f140])).

fof(f140,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f139,f126])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f137,f125])).

fof(f137,plain,
    ( sK1 = k1_funct_1(sK3,sK2)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f118,f34])).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK1 = k1_funct_1(sK3,X0)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f114,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f78,f74])).

fof(f74,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f78,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f155,plain,(
    ! [X4] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X4)
      | ~ r2_hidden(sK1,X4) ) ),
    inference(superposition,[],[f54,f140])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f158,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_relat_1(sK3))
    | k1_xboole_0 = k1_funct_1(sK3,sK1) ),
    inference(superposition,[],[f98,f140])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_relat_1(sK3))
      | k1_xboole_0 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f97,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f243,plain,(
    sK1 = k1_funct_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f236,f161])).

fof(f236,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_relat_1(sK3))
    | sK1 = k1_funct_1(sK3,sK1) ),
    inference(superposition,[],[f116,f140])).

fof(f116,plain,(
    ! [X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),k1_relat_1(sK3))
      | sK1 = k1_funct_1(sK3,X1) ) ),
    inference(resolution,[],[f114,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:02:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (19525)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (19521)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (19517)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (19516)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (19537)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.20/0.52  % (19526)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.52  % (19519)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.52  % (19529)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.20/0.53  % (19532)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.20/0.53  % (19515)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.53  % (19536)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.20/0.53  % (19530)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.20/0.53  % (19514)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.20/0.53  % (19532)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % (19528)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.54  % (19524)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.54  % SZS output start Proof for theBenchmark
% 1.20/0.54  fof(f245,plain,(
% 1.20/0.54    $false),
% 1.20/0.54    inference(subsumption_resolution,[],[f244,f126])).
% 1.20/0.54  fof(f126,plain,(
% 1.20/0.54    k1_xboole_0 != sK1),
% 1.20/0.54    inference(backward_demodulation,[],[f35,f125])).
% 1.20/0.54  fof(f125,plain,(
% 1.20/0.54    k1_xboole_0 = k1_funct_1(sK3,sK2)),
% 1.20/0.54    inference(trivial_inequality_removal,[],[f122])).
% 1.20/0.54  fof(f122,plain,(
% 1.20/0.54    sK1 != sK1 | k1_xboole_0 = k1_funct_1(sK3,sK2)),
% 1.20/0.54    inference(superposition,[],[f35,f115])).
% 1.20/0.54  fof(f115,plain,(
% 1.20/0.54    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | k1_xboole_0 = k1_funct_1(sK3,X0)) )),
% 1.20/0.54    inference(resolution,[],[f114,f97])).
% 1.20/0.54  fof(f97,plain,(
% 1.20/0.54    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_funct_1(sK3,X0)) )),
% 1.20/0.54    inference(resolution,[],[f81,f33])).
% 1.20/0.54  fof(f33,plain,(
% 1.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.20/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  % (19530)Refutation not found, incomplete strategy% (19530)------------------------------
% 1.35/0.54  % (19530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19527)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.54  % (19522)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.35/0.54  % (19542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.54  % (19543)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.54  % (19520)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (19530)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19530)Memory used [KB]: 10746
% 1.35/0.54  % (19530)Time elapsed: 0.130 s
% 1.35/0.54  % (19530)------------------------------
% 1.35/0.54  % (19530)------------------------------
% 1.35/0.54  % (19518)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (19515)Refutation not found, incomplete strategy% (19515)------------------------------
% 1.35/0.54  % (19515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19515)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (19515)Memory used [KB]: 1791
% 1.35/0.54  % (19515)Time elapsed: 0.091 s
% 1.35/0.54  % (19515)------------------------------
% 1.35/0.54  % (19515)------------------------------
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.35/0.54    inference(flattening,[],[f14])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.35/0.54    inference(ennf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,negated_conjecture,(
% 1.35/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.35/0.54    inference(negated_conjecture,[],[f12])).
% 1.35/0.54  fof(f12,conjecture,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.35/0.54  fof(f81,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k1_funct_1(sK3,X0)) )),
% 1.35/0.54    inference(resolution,[],[f67,f53])).
% 1.35/0.54  fof(f53,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(ennf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.35/0.54  fof(f67,plain,(
% 1.35/0.54    ( ! [X3] : (~v1_relat_1(sK3) | k1_xboole_0 = k1_funct_1(sK3,X3) | r2_hidden(X3,k1_relat_1(sK3))) )),
% 1.35/0.54    inference(resolution,[],[f31,f57])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/0.54    inference(nnf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.35/0.54    inference(flattening,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    v1_funct_1(sK3)),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f114,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,X0)) )),
% 1.35/0.54    inference(resolution,[],[f100,f33])).
% 1.35/0.54  fof(f100,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,X0)) )),
% 1.35/0.54    inference(resolution,[],[f86,f80])).
% 1.35/0.54  fof(f80,plain,(
% 1.35/0.54    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK3) | sK1 = X2) )),
% 1.35/0.54    inference(resolution,[],[f77,f50])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) )),
% 1.35/0.54    inference(cnf_transformation,[],[f29])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.35/0.54    inference(flattening,[],[f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.35/0.54    inference(nnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.35/0.54  fof(f77,plain,(
% 1.35/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~r2_hidden(X0,sK3)) )),
% 1.35/0.54    inference(resolution,[],[f33,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f18])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.35/0.54  fof(f86,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.35/0.54    inference(resolution,[],[f65,f53])).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X0] : (~v1_relat_1(sK3) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.35/0.54    inference(resolution,[],[f31,f58])).
% 1.35/0.54  fof(f58,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f36])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f25])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f244,plain,(
% 1.35/0.54    k1_xboole_0 = sK1),
% 1.35/0.54    inference(forward_demodulation,[],[f243,f162])).
% 1.35/0.54  fof(f162,plain,(
% 1.35/0.54    k1_xboole_0 = k1_funct_1(sK3,sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f158,f161])).
% 1.35/0.54  fof(f161,plain,(
% 1.35/0.54    ( ! [X4] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X4)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f155,f153])).
% 1.35/0.54  fof(f153,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | r2_hidden(sK1,X0)) )),
% 1.35/0.54    inference(superposition,[],[f47,f140])).
% 1.35/0.54  fof(f140,plain,(
% 1.35/0.54    k1_xboole_0 = k1_tarski(sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f139,f126])).
% 1.35/0.54  fof(f139,plain,(
% 1.35/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = k1_tarski(sK1)),
% 1.35/0.54    inference(forward_demodulation,[],[f137,f125])).
% 1.35/0.54  fof(f137,plain,(
% 1.35/0.54    sK1 = k1_funct_1(sK3,sK2) | k1_xboole_0 = k1_tarski(sK1)),
% 1.35/0.54    inference(resolution,[],[f118,f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    r2_hidden(sK2,sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f118,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | sK1 = k1_funct_1(sK3,X0) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.35/0.54    inference(superposition,[],[f114,f84])).
% 1.35/0.54  fof(f84,plain,(
% 1.35/0.54    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.35/0.54    inference(superposition,[],[f78,f74])).
% 1.35/0.54  fof(f74,plain,(
% 1.35/0.54    k1_relat_1(sK3) = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.35/0.54    inference(resolution,[],[f33,f52])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(ennf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f75,f32])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f75,plain,(
% 1.35/0.54    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.35/0.54    inference(resolution,[],[f33,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(nnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(flattening,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.54    inference(ennf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 | r2_hidden(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f27])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 1.35/0.54    inference(nnf_transformation,[],[f5])).
% 1.35/0.54  fof(f5,axiom,(
% 1.35/0.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.35/0.54  fof(f155,plain,(
% 1.35/0.54    ( ! [X4] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X4) | ~r2_hidden(sK1,X4)) )),
% 1.35/0.54    inference(superposition,[],[f54,f140])).
% 1.35/0.54  fof(f54,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.35/0.54    inference(nnf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.35/0.54  fof(f158,plain,(
% 1.35/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_relat_1(sK3)) | k1_xboole_0 = k1_funct_1(sK3,sK1)),
% 1.35/0.54    inference(superposition,[],[f98,f140])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_relat_1(sK3)) | k1_xboole_0 = k1_funct_1(sK3,X0)) )),
% 1.35/0.54    inference(resolution,[],[f97,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f27])).
% 1.35/0.54  fof(f243,plain,(
% 1.35/0.54    sK1 = k1_funct_1(sK3,sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f236,f161])).
% 1.35/0.54  fof(f236,plain,(
% 1.35/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,sK1)),
% 1.35/0.54    inference(superposition,[],[f116,f140])).
% 1.35/0.54  fof(f116,plain,(
% 1.35/0.54    ( ! [X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),k1_relat_1(sK3)) | sK1 = k1_funct_1(sK3,X1)) )),
% 1.35/0.54    inference(resolution,[],[f114,f55])).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f30])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (19532)------------------------------
% 1.35/0.54  % (19532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (19532)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (19532)Memory used [KB]: 1918
% 1.35/0.54  % (19532)Time elapsed: 0.126 s
% 1.35/0.54  % (19532)------------------------------
% 1.35/0.54  % (19532)------------------------------
% 1.35/0.54  % (19539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.35/0.55  % (19534)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.55  % (19513)Success in time 0.181 s
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 13:04:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 779 expanded)
%              Number of leaves         :   23 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          :  397 (2698 expanded)
%              Number of equality atoms :  172 (1010 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(subsumption_resolution,[],[f306,f249])).

fof(f249,plain,(
    k1_xboole_0 != k1_tarski(k1_funct_1(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f223,f74])).

fof(f74,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f223,plain,(
    k2_relat_1(k1_xboole_0) != k1_tarski(k1_funct_1(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f181,f196])).

fof(f196,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f187,f195])).

fof(f195,plain,(
    k1_xboole_0 = k11_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f193,f147])).

fof(f147,plain,(
    k2_relat_1(sK3) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[],[f146,f133])).

fof(f133,plain,(
    ! [X0] : k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0)) ),
    inference(resolution,[],[f80,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f96,f70])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f52])).

% (23949)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (23947)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (23940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f52,plain,
    ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f146,plain,(
    k9_relat_1(sK3,k1_tarski(sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[],[f135,f145])).

fof(f145,plain,(
    sK3 = k7_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f139,f132])).

fof(f132,plain,(
    v4_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f98,f70])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f139,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | sK3 = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f87,f122])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f135,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f82,f122])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f193,plain,
    ( k2_relat_1(sK3) != k11_relat_1(sK3,sK1)
    | k1_xboole_0 = k11_relat_1(sK3,sK1) ),
    inference(superposition,[],[f181,f192])).

fof(f192,plain,(
    ! [X1] :
      ( k11_relat_1(sK3,X1) = k1_tarski(k1_funct_1(sK3,X1))
      | k1_xboole_0 = k11_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f190,f158])).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK3))
      | k1_xboole_0 = k11_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f84,f122])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f190,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k11_relat_1(sK3,X0) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f189,f122])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k11_relat_1(sK3,X0) = k1_tarski(k1_funct_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f85,f68])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f187,plain,
    ( k1_xboole_0 != k11_relat_1(sK3,sK1)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f185,f133])).

fof(f185,plain,
    ( k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK1))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f184,f122])).

fof(f184,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK1)) ),
    inference(superposition,[],[f137,f145])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK3,X0))
      | k1_xboole_0 = k7_relat_1(sK3,X0)
      | k1_xboole_0 != k9_relat_1(sK3,X0) ) ),
    inference(superposition,[],[f79,f135])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

% (23931)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f181,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f72,f179])).

fof(f179,plain,(
    k2_relset_1(k1_tarski(sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f97,f70])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f72,plain,(
    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f306,plain,(
    k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK1)) ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f263,f293])).

fof(f293,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f288,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f90,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f288,plain,(
    ! [X2] : r1_tarski(k1_tarski(sK1),X2) ),
    inference(trivial_inequality_removal,[],[f287])).

fof(f287,plain,(
    ! [X2] :
      ( k1_tarski(sK1) != k1_tarski(sK1)
      | r1_tarski(k1_tarski(sK1),X2) ) ),
    inference(superposition,[],[f284,f278])).

fof(f278,plain,(
    k1_tarski(sK1) = k1_relset_1(k1_tarski(sK1),sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f276,f71])).

fof(f71,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f276,plain,
    ( k1_xboole_0 = sK2
    | k1_tarski(sK1) = k1_relset_1(k1_tarski(sK1),sK2,k1_xboole_0) ),
    inference(resolution,[],[f265,f199])).

fof(f199,plain,(
    v1_funct_2(k1_xboole_0,k1_tarski(sK1),sK2) ),
    inference(backward_demodulation,[],[f69,f196])).

fof(f69,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f99,f149])).

fof(f149,plain,(
    ! [X0,X1] : sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f103,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,k1_xboole_0) != X0
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f283,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_relset_1(X1,X2,k1_xboole_0) != X1 ) ),
    inference(subsumption_resolution,[],[f282,f155])).

fof(f155,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f154,f73])).

fof(f73,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f154,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f153,f144])).

fof(f144,plain,(
    ! [X1] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f134,f143])).

fof(f143,plain,(
    ! [X1] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f142,f74])).

fof(f142,plain,(
    ! [X1] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f136,f141])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f140,f131])).

fof(f131,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f98,f76])).

fof(f140,plain,(
    ! [X1] :
      ( ~ v4_relat_1(k1_xboole_0,X1)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f87,f121])).

fof(f121,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f96,f76])).

fof(f136,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(k1_xboole_0,X1)) = k9_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f82,f121])).

fof(f134,plain,(
    ! [X1] : k11_relat_1(k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,k1_tarski(X1)) ),
    inference(resolution,[],[f80,f121])).

fof(f153,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 != k11_relat_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f83,f121])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 != k11_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_relset_1(X1,X2,k1_xboole_0) != X1
      | r2_hidden(k4_tarski(X0,sK5(k1_xboole_0,X0)),k1_xboole_0) ) ),
    inference(resolution,[],[f108,f76])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
            & r2_hidden(sK6(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK6(X1,X2),X6),X2)
        & r2_hidden(sK6(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f263,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,X0)) ) ),
    inference(forward_demodulation,[],[f262,f74])).

fof(f262,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f261,f121])).

fof(f261,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f260,f198])).

fof(f198,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f68,f196])).

fof(f260,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f86,f73])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23944)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (23936)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (23937)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (23928)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (23926)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (23923)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23922)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (23929)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (23927)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (23945)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (23924)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (23921)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (23925)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23932)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (23928)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f306,f249])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    k1_xboole_0 != k1_tarski(k1_funct_1(k1_xboole_0,sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f223,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    k2_relat_1(k1_xboole_0) != k1_tarski(k1_funct_1(k1_xboole_0,sK1))),
% 0.22/0.54    inference(backward_demodulation,[],[f181,f196])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f187,f195])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    k1_xboole_0 = k11_relat_1(sK3,sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f193,f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    k2_relat_1(sK3) = k11_relat_1(sK3,sK1)),
% 0.22/0.54    inference(superposition,[],[f146,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X0] : (k11_relat_1(sK3,X0) = k9_relat_1(sK3,k1_tarski(X0))) )),
% 0.22/0.54    inference(resolution,[],[f80,f122])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    v1_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f96,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f52])).
% 0.22/0.54  % (23949)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (23947)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (23940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1)) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f23])).
% 0.22/0.54  fof(f23,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    k9_relat_1(sK3,k1_tarski(sK1)) = k2_relat_1(sK3)),
% 0.22/0.54    inference(superposition,[],[f135,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    sK3 = k7_relat_1(sK3,k1_tarski(sK1))),
% 0.22/0.54    inference(resolution,[],[f139,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    v4_relat_1(sK3,k1_tarski(sK1))),
% 0.22/0.54    inference(resolution,[],[f98,f70])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) )),
% 0.22/0.54    inference(resolution,[],[f87,f122])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)) )),
% 0.22/0.54    inference(resolution,[],[f82,f122])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    k2_relat_1(sK3) != k11_relat_1(sK3,sK1) | k1_xboole_0 = k11_relat_1(sK3,sK1)),
% 0.22/0.54    inference(superposition,[],[f181,f192])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ( ! [X1] : (k11_relat_1(sK3,X1) = k1_tarski(k1_funct_1(sK3,X1)) | k1_xboole_0 = k11_relat_1(sK3,X1)) )),
% 0.22/0.54    inference(resolution,[],[f190,f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK3)) | k1_xboole_0 = k11_relat_1(sK3,X0)) )),
% 0.22/0.54    inference(resolution,[],[f84,f122])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k11_relat_1(sK3,X0) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f189,f122])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | k11_relat_1(sK3,X0) = k1_tarski(k1_funct_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 0.22/0.54    inference(resolution,[],[f85,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f52])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    k1_xboole_0 != k11_relat_1(sK3,sK1) | k1_xboole_0 = sK3),
% 0.22/0.54    inference(superposition,[],[f185,f133])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK1)) | k1_xboole_0 = sK3),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f122])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ~v1_relat_1(sK3) | k1_xboole_0 = sK3 | k1_xboole_0 != k9_relat_1(sK3,k1_tarski(sK1))),
% 0.22/0.54    inference(superposition,[],[f137,f145])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | k1_xboole_0 = k7_relat_1(sK3,X0) | k1_xboole_0 != k9_relat_1(sK3,X0)) )),
% 0.22/0.54    inference(superposition,[],[f79,f135])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  % (23931)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)),
% 0.22/0.54    inference(backward_demodulation,[],[f72,f179])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    k2_relset_1(k1_tarski(sK1),sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.54    inference(resolution,[],[f97,f70])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    k2_relset_1(k1_tarski(sK1),sK2,sK3) != k1_tarski(k1_funct_1(sK3,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f52])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK1))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f305])).
% 0.22/0.54  fof(f305,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,sK1))),
% 0.22/0.54    inference(superposition,[],[f263,f293])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    k1_xboole_0 = k1_tarski(sK1)),
% 0.22/0.54    inference(resolution,[],[f288,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(resolution,[],[f90,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(flattening,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f288,plain,(
% 0.22/0.55    ( ! [X2] : (r1_tarski(k1_tarski(sK1),X2)) )),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f287])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    ( ! [X2] : (k1_tarski(sK1) != k1_tarski(sK1) | r1_tarski(k1_tarski(sK1),X2)) )),
% 0.22/0.55    inference(superposition,[],[f284,f278])).
% 0.22/0.55  fof(f278,plain,(
% 0.22/0.55    k1_tarski(sK1) = k1_relset_1(k1_tarski(sK1),sK2,k1_xboole_0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f276,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    k1_xboole_0 != sK2),
% 0.22/0.55    inference(cnf_transformation,[],[f52])).
% 0.22/0.55  fof(f276,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | k1_tarski(sK1) = k1_relset_1(k1_tarski(sK1),sK2,k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f265,f199])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    v1_funct_2(k1_xboole_0,k1_tarski(sK1),sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f69,f196])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f52])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,k1_xboole_0) = X0) )),
% 0.22/0.55    inference(resolution,[],[f99,f149])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sP0(X0,k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f103,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(definition_folding,[],[f45,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.55    inference(rectify,[],[f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f49])).
% 0.22/0.55  fof(f284,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) != X0 | r1_tarski(X0,X2)) )),
% 0.22/0.55    inference(resolution,[],[f283,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f283,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | k1_relset_1(X1,X2,k1_xboole_0) != X1) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f282,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f154,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f144])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f134,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f142,f74])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    ( ! [X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f136,f141])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f140,f131])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f98,f76])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X1] : (~v4_relat_1(k1_xboole_0,X1) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f87,f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    v1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(resolution,[],[f96,f76])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X1] : (k2_relat_1(k7_relat_1(k1_xboole_0,X1)) = k9_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f82,f121])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    ( ! [X1] : (k11_relat_1(k1_xboole_0,X1) = k9_relat_1(k1_xboole_0,k1_tarski(X1))) )),
% 0.22/0.55    inference(resolution,[],[f80,f121])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | k1_xboole_0 != k11_relat_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f83,f121])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 != k11_relat_1(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f53])).
% 0.22/0.55  fof(f282,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | k1_relset_1(X1,X2,k1_xboole_0) != X1 | r2_hidden(k4_tarski(X0,sK5(k1_xboole_0,X0)),k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f108,f76])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f64,f66,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK6(X1,X2),X6),X2) & r2_hidden(sK6(X1,X2),X1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.55    inference(rectify,[],[f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.55    inference(nnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.22/0.55  fof(f263,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | k1_xboole_0 = k1_tarski(k1_funct_1(k1_xboole_0,X0))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f262,f74])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f261,f121])).
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f260,f198])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    v1_funct_1(k1_xboole_0)),
% 0.22/0.55    inference(backward_demodulation,[],[f68,f196])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | k2_relat_1(k1_xboole_0) = k1_tarski(k1_funct_1(k1_xboole_0,X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f86,f73])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (23928)------------------------------
% 0.22/0.55  % (23928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23928)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (23928)Memory used [KB]: 6396
% 0.22/0.55  % (23928)Time elapsed: 0.089 s
% 0.22/0.55  % (23928)------------------------------
% 0.22/0.55  % (23928)------------------------------
% 0.22/0.55  % (23938)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (23942)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (23941)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (23938)Refutation not found, incomplete strategy% (23938)------------------------------
% 0.22/0.55  % (23938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23938)Memory used [KB]: 10746
% 0.22/0.55  % (23938)Time elapsed: 0.136 s
% 0.22/0.55  % (23938)------------------------------
% 0.22/0.55  % (23938)------------------------------
% 0.22/0.55  % (23939)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (23920)Success in time 0.188 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:23 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 233 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  172 ( 940 expanded)
%              Number of equality atoms :   70 ( 514 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f278,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f277])).

fof(f277,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f131,f216])).

fof(f216,plain,(
    sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f206,f113])).

fof(f113,plain,(
    sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f111,f101])).

fof(f101,plain,(
    sK0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f100,f77])).

fof(f77,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(forward_demodulation,[],[f74,f34])).

fof(f34,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

% (31477)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% (31482)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (31464)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (31476)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (31485)Refutation not found, incomplete strategy% (31485)------------------------------
% (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31483)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (31462)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% (31484)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (31485)Termination reason: Refutation not found, incomplete strategy

% (31485)Memory used [KB]: 10618
% (31485)Time elapsed: 0.120 s
% (31485)------------------------------
% (31485)------------------------------
fof(f30,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    & sK0 = k2_relset_1(sK0,sK0,sK2)
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
          & sK0 = k2_relset_1(sK0,sK0,X2)
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
        & sK0 = k2_relset_1(sK0,sK0,X2)
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
   => ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
      & sK0 = k2_relset_1(sK0,sK0,sK2)
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f74,plain,(
    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f100,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) ),
    inference(superposition,[],[f63,f96])).

fof(f96,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f93,f53])).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f92,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f90,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f87,f68])).

fof(f68,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f63,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3) ),
    inference(resolution,[],[f40,f53])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f111,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f83,f53])).

fof(f83,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k2_relat_1(k5_relat_1(sK2,X4)) = k9_relat_1(X4,sK0) ) ),
    inference(backward_demodulation,[],[f67,f82])).

fof(f82,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f75,f35])).

fof(f35,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k2_relat_1(k5_relat_1(sK2,X4)) = k9_relat_1(X4,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f206,plain,(
    k2_relat_1(k5_relat_1(sK2,sK1)) = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f168,f45])).

fof(f168,plain,(
    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f164,f128])).

fof(f128,plain,(
    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f98,f32])).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k4_relset_1(sK0,sK0,X4,X5,sK2,X3) = k5_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f164,plain,(
    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f108,f32])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k4_relset_1(sK0,sK0,X4,X5,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) ) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f131,plain,(
    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f36,f128])).

fof(f36,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:06:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (31470)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (31478)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (31466)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (31468)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (31472)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (31472)Refutation not found, incomplete strategy% (31472)------------------------------
% 0.22/0.52  % (31472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31472)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31472)Memory used [KB]: 10618
% 0.22/0.52  % (31472)Time elapsed: 0.090 s
% 0.22/0.52  % (31472)------------------------------
% 0.22/0.52  % (31472)------------------------------
% 0.22/0.52  % (31463)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (31479)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.53  % (31474)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (31475)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (31467)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (31471)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (31469)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (31469)Refutation not found, incomplete strategy% (31469)------------------------------
% 0.22/0.53  % (31469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (31469)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31469)Memory used [KB]: 6140
% 0.22/0.53  % (31469)Time elapsed: 0.107 s
% 0.22/0.53  % (31469)------------------------------
% 0.22/0.53  % (31469)------------------------------
% 0.22/0.53  % (31485)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.29/0.54  % (31471)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f278,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(trivial_inequality_removal,[],[f277])).
% 1.29/0.54  fof(f277,plain,(
% 1.29/0.54    sK0 != sK0),
% 1.29/0.54    inference(superposition,[],[f131,f216])).
% 1.29/0.54  fof(f216,plain,(
% 1.29/0.54    sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 1.29/0.54    inference(forward_demodulation,[],[f206,f113])).
% 1.29/0.54  fof(f113,plain,(
% 1.29/0.54    sK0 = k2_relat_1(k5_relat_1(sK2,sK1))),
% 1.29/0.54    inference(forward_demodulation,[],[f111,f101])).
% 1.29/0.54  fof(f101,plain,(
% 1.29/0.54    sK0 = k9_relat_1(sK1,sK0)),
% 1.29/0.54    inference(forward_demodulation,[],[f100,f77])).
% 1.29/0.54  fof(f77,plain,(
% 1.29/0.54    sK0 = k2_relat_1(sK1)),
% 1.29/0.54    inference(forward_demodulation,[],[f74,f34])).
% 1.29/0.54  fof(f34,plain,(
% 1.29/0.54    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.29/0.54    inference(cnf_transformation,[],[f30])).
% 1.29/0.54  % (31477)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.29/0.54  % (31482)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.29/0.54  % (31464)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.29/0.54  % (31476)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.29/0.54  % (31485)Refutation not found, incomplete strategy% (31485)------------------------------
% 1.29/0.54  % (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (31483)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.29/0.54  % (31462)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.29/0.55  % (31484)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.29/0.55  % (31485)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (31485)Memory used [KB]: 10618
% 1.29/0.55  % (31485)Time elapsed: 0.120 s
% 1.29/0.55  % (31485)------------------------------
% 1.29/0.55  % (31485)------------------------------
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) => (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f15,plain,(
% 1.49/0.55    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.49/0.55    inference(flattening,[],[f14])).
% 1.49/0.55  fof(f14,plain,(
% 1.49/0.55    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.49/0.55    inference(ennf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 1.49/0.55    inference(negated_conjecture,[],[f12])).
% 1.49/0.55  fof(f12,conjecture,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).
% 1.49/0.55  fof(f74,plain,(
% 1.49/0.55    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)),
% 1.49/0.55    inference(resolution,[],[f45,f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f22])).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.49/0.55  fof(f100,plain,(
% 1.49/0.55    k2_relat_1(sK1) = k9_relat_1(sK1,sK0)),
% 1.49/0.55    inference(superposition,[],[f63,f96])).
% 1.49/0.55  fof(f96,plain,(
% 1.49/0.55    sK1 = k7_relat_1(sK1,sK0)),
% 1.49/0.55    inference(resolution,[],[f93,f53])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    v1_relat_1(sK1)),
% 1.49/0.55    inference(resolution,[],[f52,f32])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.49/0.55    inference(resolution,[],[f38,f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.49/0.55  fof(f93,plain,(
% 1.49/0.55    ~v1_relat_1(sK1) | sK1 = k7_relat_1(sK1,sK0)),
% 1.49/0.55    inference(resolution,[],[f92,f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(flattening,[],[f19])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.49/0.55  fof(f92,plain,(
% 1.49/0.55    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.49/0.55    inference(resolution,[],[f90,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f31])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.55    inference(nnf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.55  fof(f90,plain,(
% 1.49/0.55    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f87,f68])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.49/0.55    inference(resolution,[],[f44,f32])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f21])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.55  fof(f87,plain,(
% 1.49/0.55    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 1.49/0.55    inference(resolution,[],[f46,f32])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f23])).
% 1.49/0.55  fof(f23,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    ( ! [X3] : (k2_relat_1(k7_relat_1(sK1,X3)) = k9_relat_1(sK1,X3)) )),
% 1.49/0.55    inference(resolution,[],[f40,f53])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.49/0.55  fof(f111,plain,(
% 1.49/0.55    k9_relat_1(sK1,sK0) = k2_relat_1(k5_relat_1(sK2,sK1))),
% 1.49/0.55    inference(resolution,[],[f83,f53])).
% 1.49/0.55  fof(f83,plain,(
% 1.49/0.55    ( ! [X4] : (~v1_relat_1(X4) | k2_relat_1(k5_relat_1(sK2,X4)) = k9_relat_1(X4,sK0)) )),
% 1.49/0.55    inference(backward_demodulation,[],[f67,f82])).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    sK0 = k2_relat_1(sK2)),
% 1.49/0.55    inference(forward_demodulation,[],[f75,f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f75,plain,(
% 1.49/0.55    k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)),
% 1.49/0.55    inference(resolution,[],[f45,f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f67,plain,(
% 1.49/0.55    ( ! [X4] : (~v1_relat_1(X4) | k2_relat_1(k5_relat_1(sK2,X4)) = k9_relat_1(X4,k2_relat_1(sK2))) )),
% 1.49/0.55    inference(resolution,[],[f37,f54])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    v1_relat_1(sK2)),
% 1.49/0.55    inference(resolution,[],[f52,f33])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f16])).
% 1.49/0.55  fof(f16,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.49/0.55  fof(f206,plain,(
% 1.49/0.55    k2_relat_1(k5_relat_1(sK2,sK1)) = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 1.49/0.55    inference(resolution,[],[f168,f45])).
% 1.49/0.55  fof(f168,plain,(
% 1.49/0.55    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.55    inference(forward_demodulation,[],[f164,f128])).
% 1.49/0.55  fof(f128,plain,(
% 1.49/0.55    k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)),
% 1.49/0.55    inference(resolution,[],[f98,f32])).
% 1.49/0.55  fof(f98,plain,(
% 1.49/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k4_relset_1(sK0,sK0,X4,X5,sK2,X3) = k5_relat_1(sK2,X3)) )),
% 1.49/0.55    inference(resolution,[],[f47,f33])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(flattening,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.55    inference(ennf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.49/0.55  fof(f164,plain,(
% 1.49/0.55    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.55    inference(resolution,[],[f108,f32])).
% 1.49/0.55  fof(f108,plain,(
% 1.49/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | m1_subset_1(k4_relset_1(sK0,sK0,X4,X5,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))) )),
% 1.49/0.55    inference(resolution,[],[f48,f33])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f27])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(flattening,[],[f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.49/0.55  fof(f131,plain,(
% 1.49/0.55    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 1.49/0.55    inference(backward_demodulation,[],[f36,f128])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (31471)------------------------------
% 1.49/0.55  % (31471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (31471)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (31471)Memory used [KB]: 1791
% 1.49/0.55  % (31471)Time elapsed: 0.066 s
% 1.49/0.55  % (31471)------------------------------
% 1.49/0.55  % (31471)------------------------------
% 1.49/0.55  % (31461)Success in time 0.186 s
%------------------------------------------------------------------------------

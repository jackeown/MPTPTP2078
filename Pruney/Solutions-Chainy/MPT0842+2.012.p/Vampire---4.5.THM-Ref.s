%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 163 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 714 expanded)
%              Number of equality atoms :    4 (  20 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f41])).

fof(f41,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f157,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f156,f136])).

fof(f136,plain,(
    r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f135,f83])).

fof(f83,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(backward_demodulation,[],[f21,f78])).

fof(f78,plain,(
    ! [X0] : k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK2,sK3,X0) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f21,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f135,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ r2_hidden(sK5,sK1) ),
    inference(factoring,[],[f128])).

fof(f128,plain,(
    ! [X9] :
      ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | r2_hidden(sK4,k10_relat_1(sK3,X9))
      | ~ r2_hidden(sK5,X9) ) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,(
    ! [X9] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK5,X9)
      | r2_hidden(sK4,k10_relat_1(sK3,X9))
      | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f40,f82])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(backward_demodulation,[],[f20,f78])).

fof(f20,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f156,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f154,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f153,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1,sK3),sK2)
      | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    inference(resolution,[],[f69,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f69,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK6(X8,X9,sK3),sK2)
      | ~ r2_hidden(X8,k10_relat_1(sK3,X9)) ) ),
    inference(subsumption_resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(X8,k10_relat_1(sK3,X9))
      | r2_hidden(sK6(X8,X9,sK3),sK2) ) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK3)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f152,f41])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK4,X0,sK3),sK2)
      | ~ r2_hidden(sK6(sK4,X0,sK3),sK1)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f151,f32])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
      | ~ m1_subset_1(X0,sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f80,f136])).

fof(f80,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
      | ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(backward_demodulation,[],[f18,f78])).

fof(f18,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (15899)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.46  % (15891)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (15879)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.48  % (15902)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.48  % (15884)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (15890)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (15895)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (15883)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (15895)Refutation not found, incomplete strategy% (15895)------------------------------
% 0.20/0.49  % (15895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15895)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15895)Memory used [KB]: 1663
% 0.20/0.49  % (15895)Time elapsed: 0.079 s
% 0.20/0.49  % (15895)------------------------------
% 0.20/0.49  % (15895)------------------------------
% 0.20/0.49  % (15901)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.49  % (15893)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % (15892)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (15882)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (15900)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (15882)Refutation not found, incomplete strategy% (15882)------------------------------
% 0.20/0.50  % (15882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15882)Memory used [KB]: 10618
% 0.20/0.50  % (15882)Time elapsed: 0.086 s
% 0.20/0.50  % (15882)------------------------------
% 0.20/0.50  % (15882)------------------------------
% 0.20/0.50  % (15887)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (15896)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (15886)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (15889)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (15881)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (15897)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (15885)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  % (15880)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  % (15892)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f157,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    v1_relat_1(sK3)),
% 0.20/0.52    inference(resolution,[],[f35,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    ~v1_relat_1(sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f136])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f135,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f21,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0] : (k10_relat_1(sK3,X0) = k8_relset_1(sK0,sK2,sK3,X0)) )),
% 0.20/0.52    inference(resolution,[],[f36,f23])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(sK5,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~r2_hidden(sK5,sK1)),
% 0.20/0.52    inference(factoring,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X9] : (r2_hidden(sK4,k10_relat_1(sK3,sK1)) | r2_hidden(sK4,k10_relat_1(sK3,X9)) | ~r2_hidden(sK5,X9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f125,f41])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X9] : (~v1_relat_1(sK3) | ~r2_hidden(sK5,X9) | r2_hidden(sK4,k10_relat_1(sK3,X9)) | r2_hidden(sK4,k10_relat_1(sK3,sK1))) )),
% 0.20/0.52    inference(resolution,[],[f40,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.20/0.52    inference(backward_demodulation,[],[f20,f78])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X3),X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f34,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1))),
% 0.20/0.52    inference(resolution,[],[f154,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1,sK3),sK2) | ~r2_hidden(X0,k10_relat_1(sK3,X1))) )),
% 0.20/0.52    inference(resolution,[],[f69,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X8,X9] : (r2_hidden(sK6(X8,X9,sK3),sK2) | ~r2_hidden(X8,k10_relat_1(sK3,X9))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f41])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X8,X9] : (~v1_relat_1(sK3) | ~r2_hidden(X8,k10_relat_1(sK3,X9)) | r2_hidden(sK6(X8,X9,sK3),sK2)) )),
% 0.20/0.52    inference(resolution,[],[f32,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK3) | r2_hidden(X0,sK2)) )),
% 0.20/0.52    inference(resolution,[],[f38,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.20/0.52    inference(resolution,[],[f28,f23])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f152,f41])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK6(sK4,X0,sK3),sK2) | ~r2_hidden(sK6(sK4,X0,sK3),sK1) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) )),
% 0.20/0.52    inference(resolution,[],[f151,f32])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~m1_subset_1(X0,sK2) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.52    inference(resolution,[],[f80,f136])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X5] : (~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f18,f78])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15892)------------------------------
% 0.20/0.52  % (15892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15892)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15892)Memory used [KB]: 6268
% 0.20/0.52  % (15892)Time elapsed: 0.097 s
% 0.20/0.52  % (15892)------------------------------
% 0.20/0.52  % (15892)------------------------------
% 0.20/0.52  % (15888)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (15878)Success in time 0.166 s
%------------------------------------------------------------------------------

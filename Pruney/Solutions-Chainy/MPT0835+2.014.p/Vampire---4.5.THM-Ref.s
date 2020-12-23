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
% DateTime   : Thu Dec  3 12:57:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 203 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 ( 543 expanded)
%              Number of equality atoms :   90 ( 248 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f176,f178,f194,f233])).

fof(f233,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f231,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

% (12260)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

% (12271)Refutation not found, incomplete strategy% (12271)------------------------------
% (12271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12271)Termination reason: Refutation not found, incomplete strategy

% (12271)Memory used [KB]: 6140
% (12271)Time elapsed: 0.091 s
% (12271)------------------------------
% (12271)------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f231,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f229,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f229,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f228,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f227,f71])).

fof(f71,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f227,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | spl3_2 ),
    inference(superposition,[],[f226,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f82,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f81,f72])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f226,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f225,f38])).

% (12274)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f225,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f221,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f221,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f220,f126])).

fof(f126,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(resolution,[],[f124,f38])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k9_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f51,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f220,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f217,f38])).

fof(f217,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f69,f57])).

fof(f69,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f194,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f189,f38])).

fof(f189,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_4 ),
    inference(superposition,[],[f95,f51])).

fof(f95,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_4
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f178,plain,
    ( ~ spl3_6
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f177,f63,f93,f114])).

fof(f114,plain,
    ( spl3_6
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( spl3_1
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f177,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f145,f71])).

fof(f145,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1 ),
    inference(superposition,[],[f144,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

% (12265)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (12278)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f144,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f142,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f137,f52])).

fof(f137,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relset_1(sK1,sK0,sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f131,f38])).

% (12275)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f131,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relset_1(sK1,sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f85,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f84,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f65,f57])).

fof(f65,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f176,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f161,f114])).

fof(f161,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f156,f60])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f151,f38])).

% (12276)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (12273)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (12269)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (12269)Refutation not found, incomplete strategy% (12269)------------------------------
% (12269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12269)Termination reason: Refutation not found, incomplete strategy

% (12269)Memory used [KB]: 10618
% (12269)Time elapsed: 0.064 s
% (12269)------------------------------
% (12269)------------------------------
% (12263)Refutation not found, incomplete strategy% (12263)------------------------------
% (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12263)Termination reason: Refutation not found, incomplete strategy

% (12263)Memory used [KB]: 6140
% (12263)Time elapsed: 0.089 s
% (12263)------------------------------
% (12263)------------------------------
% (12261)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (12280)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f151,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(k1_relat_1(X8),X9)
      | v4_relat_1(X8,X9) ) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f70,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f67,f63])).

fof(f39,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (12266)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (12262)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.49  % (12268)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.49  % (12263)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  % (12259)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (12277)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % (12267)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.49  % (12259)Refutation not found, incomplete strategy% (12259)------------------------------
% 0.19/0.49  % (12259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12259)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (12259)Memory used [KB]: 10618
% 0.19/0.49  % (12259)Time elapsed: 0.087 s
% 0.19/0.49  % (12259)------------------------------
% 0.19/0.49  % (12259)------------------------------
% 0.19/0.49  % (12264)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.49  % (12264)Refutation not found, incomplete strategy% (12264)------------------------------
% 0.19/0.49  % (12264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (12264)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (12264)Memory used [KB]: 10618
% 0.19/0.49  % (12264)Time elapsed: 0.087 s
% 0.19/0.49  % (12264)------------------------------
% 0.19/0.49  % (12264)------------------------------
% 0.19/0.49  % (12281)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.49  % (12271)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (12262)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f234,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f70,f176,f178,f194,f233])).
% 0.19/0.50  fof(f233,plain,(
% 0.19/0.50    spl3_2),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f232])).
% 0.19/0.50  fof(f232,plain,(
% 0.19/0.50    $false | spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f231,f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  % (12260)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.50    inference(ennf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.19/0.50    inference(negated_conjecture,[],[f16])).
% 0.19/0.50  % (12271)Refutation not found, incomplete strategy% (12271)------------------------------
% 0.19/0.50  % (12271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (12271)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (12271)Memory used [KB]: 6140
% 0.19/0.50  % (12271)Time elapsed: 0.091 s
% 0.19/0.50  % (12271)------------------------------
% 0.19/0.50  % (12271)------------------------------
% 0.19/0.50  fof(f16,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.19/0.50  fof(f231,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f230])).
% 0.19/0.50  fof(f230,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.19/0.50    inference(superposition,[],[f229,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.50  fof(f229,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f228,f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.50    inference(flattening,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.50    inference(nnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.50  fof(f228,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f227,f71])).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    v1_relat_1(sK2)),
% 0.19/0.50    inference(resolution,[],[f50,f38])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | spl3_2),
% 0.19/0.50    inference(superposition,[],[f226,f83])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f82,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f81,f72])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.50    inference(resolution,[],[f50,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,axiom,(
% 0.19/0.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f80])).
% 0.19/0.50  fof(f80,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(superposition,[],[f43,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.19/0.50  fof(f226,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f225,f38])).
% 0.19/0.50  % (12274)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.50  fof(f225,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.19/0.50    inference(superposition,[],[f221,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.50  fof(f221,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl3_2),
% 0.19/0.50    inference(forward_demodulation,[],[f220,f126])).
% 0.19/0.50  fof(f126,plain,(
% 0.19/0.50    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.19/0.50    inference(resolution,[],[f124,f38])).
% 0.19/0.50  fof(f124,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k9_relat_1(X2,X0)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f123])).
% 0.19/0.50  fof(f123,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(superposition,[],[f51,f105])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(superposition,[],[f57,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.50  fof(f220,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 0.19/0.50    inference(subsumption_resolution,[],[f217,f38])).
% 0.19/0.50  fof(f217,plain,(
% 0.19/0.50    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.19/0.50    inference(superposition,[],[f69,f57])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl3_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    spl3_2 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    spl3_4),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f193])).
% 0.19/0.50  fof(f193,plain,(
% 0.19/0.50    $false | spl3_4),
% 0.19/0.50    inference(subsumption_resolution,[],[f189,f38])).
% 0.19/0.50  fof(f189,plain,(
% 0.19/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_4),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f188])).
% 0.19/0.50  fof(f188,plain,(
% 0.19/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_4),
% 0.19/0.50    inference(superposition,[],[f95,f51])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | spl3_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f93])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    spl3_4 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.50  fof(f178,plain,(
% 0.19/0.50    ~spl3_6 | ~spl3_4 | spl3_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f177,f63,f93,f114])).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    spl3_6 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    spl3_1 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK2)) | spl3_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f145,f71])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK2)) | spl3_1),
% 0.19/0.50    inference(superposition,[],[f144,f79])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f78])).
% 0.19/0.50  fof(f78,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.50    inference(superposition,[],[f44,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.50  % (12265)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.50  % (12278)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.50  fof(f144,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | spl3_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f142,f38])).
% 0.19/0.50  fof(f142,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.19/0.50    inference(superposition,[],[f137,f52])).
% 0.19/0.50  fof(f137,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relset_1(sK1,sK0,sK2)) | spl3_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f131,f38])).
% 0.19/0.50  % (12275)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  fof(f131,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.19/0.50    inference(superposition,[],[f85,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_1),
% 0.19/0.50    inference(subsumption_resolution,[],[f84,f38])).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.19/0.50    inference(superposition,[],[f65,f57])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl3_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f63])).
% 0.19/0.50  fof(f176,plain,(
% 0.19/0.50    spl3_6),
% 0.19/0.50    inference(avatar_split_clause,[],[f161,f114])).
% 0.19/0.50  fof(f161,plain,(
% 0.19/0.50    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.19/0.50    inference(resolution,[],[f156,f60])).
% 0.19/0.50  fof(f156,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v4_relat_1(sK2,X0)) )),
% 0.19/0.50    inference(resolution,[],[f151,f38])).
% 0.19/0.50  % (12276)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (12273)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.50  % (12269)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (12269)Refutation not found, incomplete strategy% (12269)------------------------------
% 0.19/0.50  % (12269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (12269)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (12269)Memory used [KB]: 10618
% 0.19/0.50  % (12269)Time elapsed: 0.064 s
% 0.19/0.50  % (12269)------------------------------
% 0.19/0.50  % (12269)------------------------------
% 0.19/0.51  % (12263)Refutation not found, incomplete strategy% (12263)------------------------------
% 0.19/0.51  % (12263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12263)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12263)Memory used [KB]: 6140
% 0.19/0.51  % (12263)Time elapsed: 0.089 s
% 0.19/0.51  % (12263)------------------------------
% 0.19/0.51  % (12263)------------------------------
% 0.19/0.51  % (12261)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.51  % (12280)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.51  fof(f151,plain,(
% 0.19/0.51    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~r1_tarski(k1_relat_1(X8),X9) | v4_relat_1(X8,X9)) )),
% 0.19/0.51    inference(resolution,[],[f59,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.51    inference(flattening,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ~spl3_1 | ~spl3_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f39,f67,f63])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (12262)------------------------------
% 0.19/0.51  % (12262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12262)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (12262)Memory used [KB]: 6268
% 0.19/0.51  % (12262)Time elapsed: 0.090 s
% 0.19/0.51  % (12262)------------------------------
% 0.19/0.51  % (12262)------------------------------
% 1.22/0.51  % (12257)Success in time 0.157 s
%------------------------------------------------------------------------------

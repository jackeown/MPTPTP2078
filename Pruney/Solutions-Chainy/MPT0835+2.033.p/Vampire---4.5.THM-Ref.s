%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 299 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   21
%              Number of atoms          :  319 ( 800 expanded)
%              Number of equality atoms :   92 ( 317 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f261,f354,f356,f379,f535])).

fof(f535,plain,
    ( spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f533,f247])).

fof(f247,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl3_9
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f533,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f532,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f81,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
      | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
          | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
        | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f532,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f531])).

fof(f531,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_2 ),
    inference(superposition,[],[f530,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f170,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f169,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f169,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f530,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f525,f42])).

fof(f525,plain,
    ( k10_relat_1(sK2,sK0) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f497,f284])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f66,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

% (28608)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (28613)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f497,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f496,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f496,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f495,f83])).

fof(f495,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | spl3_2 ),
    inference(superposition,[],[f494,f171])).

fof(f494,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f493,f42])).

fof(f493,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f399,f66])).

fof(f399,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f398,f312])).

fof(f312,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(resolution,[],[f298,f42])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k9_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f60,f256])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f65,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

% (28613)Refutation not found, incomplete strategy% (28613)------------------------------
% (28613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f398,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f395,f42])).

fof(f395,plain,
    ( k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_2 ),
    inference(superposition,[],[f77,f65])).

fof(f77,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_2
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f379,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f374,f42])).

fof(f374,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(superposition,[],[f216,f60])).

fof(f216,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_8
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f356,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f355,f246,f71,f214,f250])).

fof(f250,plain,
    ( spl3_10
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f71,plain,
    ( spl3_1
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f355,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f278,f83])).

fof(f278,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f277,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f277,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f276,f247])).

fof(f276,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f274,f83])).

fof(f274,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_1 ),
    inference(superposition,[],[f241,f171])).

fof(f241,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f238,f42])).

fof(f238,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f206,f66])).

fof(f206,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f205,f42])).

fof(f205,plain,
    ( k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f73,f65])).

fof(f73,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f354,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f338,f250])).

fof(f338,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f334,f68])).

fof(f334,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f301,f42])).

fof(f301,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ r1_tarski(k1_relat_1(X4),X5)
      | v4_relat_1(X4,X5) ) ),
    inference(resolution,[],[f67,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f261,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f259,f83])).

fof(f259,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(subsumption_resolution,[],[f258,f118])).

fof(f118,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f258,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f248,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f248,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f246])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f75,f71])).

fof(f43,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28620)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (28628)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.48  % (28620)Refutation not found, incomplete strategy% (28620)------------------------------
% 0.20/0.48  % (28620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (28620)Memory used [KB]: 6140
% 0.20/0.48  % (28620)Time elapsed: 0.066 s
% 0.20/0.48  % (28620)------------------------------
% 0.20/0.48  % (28620)------------------------------
% 0.20/0.51  % (28610)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (28611)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (28619)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (28611)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f536,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f78,f261,f354,f356,f379,f535])).
% 0.20/0.53  fof(f535,plain,(
% 0.20/0.53    spl3_2 | ~spl3_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f534])).
% 0.20/0.53  fof(f534,plain,(
% 0.20/0.53    $false | (spl3_2 | ~spl3_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f533,f247])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK2),sK0) | ~spl3_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f246])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    spl3_9 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.53  fof(f533,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_2),
% 0.20/0.53    inference(subsumption_resolution,[],[f532,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.20/0.53    inference(resolution,[],[f48,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    (k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f532,plain,(
% 0.20/0.53    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_2),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f531])).
% 0.20/0.53  fof(f531,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_2),
% 0.20/0.53    inference(superposition,[],[f530,f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f170,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(superposition,[],[f47,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.53  fof(f530,plain,(
% 0.20/0.53    k10_relat_1(sK2,sK0) != k1_relat_1(sK2) | spl3_2),
% 0.20/0.53    inference(subsumption_resolution,[],[f525,f42])).
% 0.20/0.53  fof(f525,plain,(
% 0.20/0.53    k10_relat_1(sK2,sK0) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.20/0.53    inference(superposition,[],[f497,f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f283])).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(superposition,[],[f66,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  % (28608)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (28613)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.54  fof(f497,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f496,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f496,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f495,f83])).
% 0.20/0.54  fof(f495,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) | spl3_2),
% 0.20/0.54    inference(superposition,[],[f494,f171])).
% 0.20/0.54  fof(f494,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f493,f42])).
% 0.20/0.54  fof(f493,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.20/0.54    inference(superposition,[],[f399,f66])).
% 0.20/0.54  fof(f399,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl3_2),
% 0.20/0.54    inference(forward_demodulation,[],[f398,f312])).
% 0.20/0.54  fof(f312,plain,(
% 0.20/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.20/0.54    inference(resolution,[],[f298,f42])).
% 0.20/0.54  fof(f298,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relat_1(X2) = k9_relat_1(X2,X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f297])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(superposition,[],[f60,f256])).
% 0.20/0.54  fof(f256,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f255])).
% 0.20/0.54  fof(f255,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k9_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(superposition,[],[f65,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  % (28613)Refutation not found, incomplete strategy% (28613)------------------------------
% 0.20/0.54  % (28613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f398,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f395,f42])).
% 0.20/0.54  fof(f395,plain,(
% 0.20/0.54    k1_relset_1(sK1,sK0,sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_2),
% 0.20/0.54    inference(superposition,[],[f77,f65])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    spl3_2 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f379,plain,(
% 0.20/0.54    spl3_8),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f378])).
% 0.20/0.54  fof(f378,plain,(
% 0.20/0.54    $false | spl3_8),
% 0.20/0.54    inference(subsumption_resolution,[],[f374,f42])).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f373])).
% 0.20/0.54  fof(f373,plain,(
% 0.20/0.54    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.20/0.54    inference(superposition,[],[f216,f60])).
% 0.20/0.54  fof(f216,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | spl3_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f214])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    spl3_8 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.54  fof(f356,plain,(
% 0.20/0.54    ~spl3_10 | ~spl3_8 | spl3_1 | ~spl3_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f355,f246,f71,f214,f250])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    spl3_10 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    spl3_1 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK2)) | (spl3_1 | ~spl3_9)),
% 0.20/0.54    inference(subsumption_resolution,[],[f278,f83])).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,k1_relat_1(sK2)) | (spl3_1 | ~spl3_9)),
% 0.20/0.54    inference(superposition,[],[f277,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f50,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.54  fof(f277,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | (spl3_1 | ~spl3_9)),
% 0.20/0.54    inference(subsumption_resolution,[],[f276,f247])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f274,f83])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_1),
% 0.20/0.54    inference(superposition,[],[f241,f171])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f238,f42])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.20/0.54    inference(superposition,[],[f206,f66])).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f205,f42])).
% 0.20/0.54  fof(f205,plain,(
% 0.20/0.54    k2_relset_1(sK1,sK0,sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.20/0.54    inference(superposition,[],[f73,f65])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f71])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    spl3_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f338,f250])).
% 0.20/0.54  fof(f338,plain,(
% 0.20/0.54    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f334,f68])).
% 0.20/0.54  fof(f334,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v4_relat_1(sK2,X0)) )),
% 0.20/0.54    inference(resolution,[],[f301,f42])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~r1_tarski(k1_relat_1(X4),X5) | v4_relat_1(X4,X5)) )),
% 0.20/0.54    inference(resolution,[],[f67,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.54    inference(flattening,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.54  fof(f261,plain,(
% 0.20/0.54    spl3_9),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f260])).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    $false | spl3_9),
% 0.20/0.54    inference(subsumption_resolution,[],[f259,f83])).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    ~v1_relat_1(sK2) | spl3_9),
% 0.20/0.54    inference(subsumption_resolution,[],[f258,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    v5_relat_1(sK2,sK0)),
% 0.20/0.54    inference(resolution,[],[f62,f42])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f258,plain,(
% 0.20/0.54    ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_9),
% 0.20/0.54    inference(resolution,[],[f248,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f246])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ~spl3_1 | ~spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f75,f71])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (28611)------------------------------
% 0.20/0.54  % (28611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (28611)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (28611)Memory used [KB]: 6396
% 0.20/0.54  % (28611)Time elapsed: 0.100 s
% 0.20/0.54  % (28611)------------------------------
% 0.20/0.54  % (28611)------------------------------
% 0.20/0.54  % (28613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (28613)Memory used [KB]: 10618
% 0.20/0.55  % (28606)Success in time 0.187 s
%------------------------------------------------------------------------------

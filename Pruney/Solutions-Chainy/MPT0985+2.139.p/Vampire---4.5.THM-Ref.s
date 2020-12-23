%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  252 (1137 expanded)
%              Number of leaves         :   34 ( 297 expanded)
%              Depth                    :   19
%              Number of atoms          :  876 (5089 expanded)
%              Number of equality atoms :  102 ( 757 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f119,f225,f492,f640,f656,f682,f686,f693,f849,f909,f934,f980,f1024,f1074,f1103,f1123])).

fof(f1123,plain,
    ( spl3_2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | spl3_2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f1117,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1117,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1116,f1076])).

fof(f1076,plain,
    ( ! [X2,X3] :
        ( v1_funct_2(k2_funct_1(X2),X2,X3)
        | ~ v1_xboole_0(X2) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1075,f1000])).

fof(f1000,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | v1_xboole_0(k2_funct_1(X4)) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f996,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f996,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | v1_xboole_0(k2_funct_1(X4))
        | ~ v1_xboole_0(k2_zfmisc_1(X4,k2_relat_1(k2_funct_1(X4)))) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f788,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f788,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0)))))
        | ~ v1_xboole_0(X0) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f787,f780])).

fof(f780,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v2_funct_1(X0) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(superposition,[],[f733,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f733,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f48,f731])).

fof(f731,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f672,f205])).

fof(f205,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f672,plain,
    ( sK1 = sK2
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl3_28
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f41])).

% (17430)Refutation not found, incomplete strategy% (17430)------------------------------
% (17430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17430)Termination reason: Refutation not found, incomplete strategy

% (17430)Memory used [KB]: 10618
% (17430)Time elapsed: 0.116 s
% (17430)------------------------------
% (17430)------------------------------
fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

% (17429)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f787,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f786,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(superposition,[],[f56,f57])).

fof(f56,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( v1_funct_1(k1_xboole_0)
    & v1_relat_1(k1_xboole_0) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f786,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f503,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f57])).

fof(f55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

fof(f503,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f144,f99])).

fof(f99,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f53,f57])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f143,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f143,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f141,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1075,plain,
    ( ! [X2,X3] :
        ( v1_funct_2(k2_funct_1(X2),X2,X3)
        | ~ v1_xboole_0(X2)
        | ~ v1_xboole_0(k2_funct_1(X2)) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1040,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f54,f57])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1040,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_funct_1(X2),X3)
        | v1_funct_2(k2_funct_1(X2),X2,X3)
        | ~ v1_xboole_0(X2)
        | ~ v1_xboole_0(k2_funct_1(X2)) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(superposition,[],[f794,f99])).

fof(f794,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
        | v1_funct_2(k2_funct_1(X0),X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f793,f780])).

fof(f793,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v2_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f792,f102])).

fof(f792,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f532,f101])).

fof(f532,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(X0),X0,X1)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f160,f99])).

fof(f160,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f159,f63])).

fof(f159,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f154,f64])).

fof(f154,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f71,f65])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1116,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(X0),X0,sK0)
        | ~ v1_xboole_0(X0) )
    | spl3_2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(superposition,[],[f1115,f57])).

fof(f1115,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f1114,f731])).

fof(f1114,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f91,f205])).

fof(f91,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1103,plain,
    ( spl3_3
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f1102])).

fof(f1102,plain,
    ( $false
    | spl3_3
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1091,f51])).

fof(f1091,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_3
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(resolution,[],[f1087,f812])).

fof(f812,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_xboole_0(X0) )
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(superposition,[],[f742,f57])).

fof(f742,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f697,f731])).

fof(f697,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f94,f205])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1087,plain,
    ( ! [X2] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1084,f54])).

fof(f1084,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f766,f1081])).

fof(f1081,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f1080,f205])).

fof(f1080,plain,
    ( sK1 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f639,f731])).

fof(f639,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl3_22
  <=> sK1 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f766,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f765,f55])).

fof(f765,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f764,f56])).

fof(f764,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f611,f733])).

fof(f611,plain,(
    ! [X2] :
      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2)
      | ~ v2_funct_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f181,f53])).

% (17422)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f181,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f180,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f175,f64])).

fof(f175,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f72,f65])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1074,plain,
    ( spl3_3
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | spl3_3
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f1071,f974])).

fof(f974,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl3_37
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1071,plain,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28 ),
    inference(resolution,[],[f1026,f100])).

fof(f1026,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),sK0)
    | spl3_3
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28 ),
    inference(resolution,[],[f853,f742])).

fof(f853,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
        | ~ r1_tarski(k2_funct_1(k1_xboole_0),X2) )
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f766,f850])).

fof(f850,plain,
    ( k2_funct_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_21
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f636,f731])).

fof(f636,plain,
    ( k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f635])).

fof(f635,plain,
    ( spl3_21
  <=> k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1024,plain,(
    spl3_38 ),
    inference(avatar_contradiction_clause,[],[f1023])).

fof(f1023,plain,
    ( $false
    | spl3_38 ),
    inference(subsumption_resolution,[],[f1019,f51])).

fof(f1019,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_38 ),
    inference(resolution,[],[f979,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f979,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl3_38
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f980,plain,
    ( spl3_37
    | ~ spl3_38
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f976,f896,f671,f204,f978,f973])).

fof(f896,plain,
    ( spl3_33
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f976,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f887,f897])).

fof(f897,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f896])).

fof(f887,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f772,f58])).

fof(f772,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f771,f55])).

fof(f771,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f770,f56])).

fof(f770,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f522,f733])).

fof(f522,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f150,f52])).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f150,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f147,f64])).

fof(f147,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0))))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f934,plain,
    ( spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f933])).

fof(f933,plain,
    ( $false
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f917,f179])).

fof(f179,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(subsumption_resolution,[],[f178,f54])).

fof(f178,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(forward_demodulation,[],[f177,f53])).

fof(f177,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f176,f55])).

fof(f176,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f174,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f72,f52])).

fof(f917,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_8
    | ~ spl3_28
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f742,f894])).

fof(f894,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f893])).

fof(f893,plain,
    ( spl3_32
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f909,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f908,f671,f204,f896,f893])).

fof(f908,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f907,f51])).

fof(f907,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f884,f778])).

fof(f778,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f777,f55])).

fof(f777,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f776,f56])).

fof(f776,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f438,f733])).

fof(f438,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f152,f52])).

fof(f152,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f151,f63])).

fof(f151,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f148,f64])).

fof(f148,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f61,f66])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f884,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f772,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | X0 = X2
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f83,f57])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f849,plain,
    ( ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f847,f51])).

fof(f847,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f846,f52])).

fof(f846,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f845,f55])).

fof(f845,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f844,f56])).

fof(f844,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f841,f733])).

fof(f841,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(superposition,[],[f737,f66])).

fof(f737,plain,
    ( ~ v1_xboole_0(k2_relat_1(k2_funct_1(k1_xboole_0)))
    | ~ spl3_8
    | spl3_20
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f633,f731])).

fof(f633,plain,
    ( ~ v1_xboole_0(k2_relat_1(k2_funct_1(sK2)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl3_20
  <=> v1_xboole_0(k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f693,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f692,f204,f201])).

fof(f201,plain,
    ( spl3_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f692,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f228,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f228,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f47,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f686,plain,
    ( ~ spl3_5
    | spl3_28 ),
    inference(avatar_split_clause,[],[f344,f671,f113])).

fof(f113,plain,
    ( spl3_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f344,plain,
    ( sK1 = sK2
    | ~ v1_xboole_0(sK2) ),
    inference(superposition,[],[f99,f163])).

fof(f163,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f161,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f73,f49])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f682,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f230,f113,f110])).

fof(f110,plain,
    ( spl3_4
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f230,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f47,f58])).

fof(f656,plain,
    ( spl3_3
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | spl3_3
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f654,f94])).

fof(f654,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f653,f241])).

fof(f241,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f237,f47])).

fof(f237,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_7 ),
    inference(superposition,[],[f202,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f202,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f201])).

fof(f653,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f652,f120])).

fof(f120,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f116,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f652,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f651,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f651,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f628,f48])).

fof(f628,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f515,f66])).

fof(f515,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f514,f120])).

fof(f514,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f513,f45])).

fof(f513,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f506,f48])).

fof(f506,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f144,f163])).

fof(f640,plain,
    ( ~ spl3_20
    | spl3_21
    | spl3_22 ),
    inference(avatar_split_clause,[],[f630,f638,f635,f632])).

fof(f630,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f624,f434])).

fof(f434,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f433,f120])).

fof(f433,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f432,f45])).

fof(f432,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f415,f48])).

fof(f415,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f146,f163])).

fof(f146,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f145,f63])).

fof(f145,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f142,f64])).

fof(f142,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f61,f65])).

fof(f624,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | sK1 = k2_relat_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(k2_relat_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f515,f183])).

fof(f492,plain,
    ( spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f490,f91])).

fof(f490,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f489,f241])).

fof(f489,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f488,f120])).

fof(f488,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f487,f45])).

fof(f487,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f485,f48])).

fof(f485,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f434,f66])).

fof(f225,plain,
    ( spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f219,f51])).

fof(f219,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f130,f205])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_4 ),
    inference(resolution,[],[f111,f68])).

fof(f111,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f119,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f117,f67])).

fof(f117,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f116,f107])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f64,f88])).

fof(f88,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f50,f93,f90,f87])).

fof(f50,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 21:08:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (17424)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (17416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (17420)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (17412)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (17414)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (17423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (17411)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (17415)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (17425)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (17426)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (17413)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (17411)Refutation not found, incomplete strategy% (17411)------------------------------
% 0.22/0.53  % (17411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17411)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17411)Memory used [KB]: 10618
% 0.22/0.53  % (17411)Time elapsed: 0.066 s
% 0.22/0.53  % (17411)------------------------------
% 0.22/0.53  % (17411)------------------------------
% 0.22/0.53  % (17417)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (17419)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (17412)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (17427)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.54  % (17410)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (17428)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (17430)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1124,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f95,f119,f225,f492,f640,f656,f682,f686,f693,f849,f909,f934,f980,f1024,f1074,f1103,f1123])).
% 0.22/0.54  fof(f1123,plain,(
% 0.22/0.54    spl3_2 | ~spl3_8 | ~spl3_28),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1118])).
% 0.22/0.54  fof(f1118,plain,(
% 0.22/0.54    $false | (spl3_2 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(resolution,[],[f1117,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f1117,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0)) ) | (spl3_2 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1116,f1076])).
% 0.22/0.54  fof(f1076,plain,(
% 0.22/0.54    ( ! [X2,X3] : (v1_funct_2(k2_funct_1(X2),X2,X3) | ~v1_xboole_0(X2)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1075,f1000])).
% 0.22/0.54  fof(f1000,plain,(
% 0.22/0.54    ( ! [X4] : (~v1_xboole_0(X4) | v1_xboole_0(k2_funct_1(X4))) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f996,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.22/0.54  fof(f996,plain,(
% 0.22/0.54    ( ! [X4] : (~v1_xboole_0(X4) | v1_xboole_0(k2_funct_1(X4)) | ~v1_xboole_0(k2_zfmisc_1(X4,k2_relat_1(k2_funct_1(X4))))) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(resolution,[],[f788,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.54  fof(f788,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0))))) | ~v1_xboole_0(X0)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f787,f780])).
% 0.22/0.54  fof(f780,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(superposition,[],[f733,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.54  fof(f733,plain,(
% 0.22/0.54    v2_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(backward_demodulation,[],[f48,f731])).
% 0.22/0.54  fof(f731,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(forward_demodulation,[],[f672,f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f204])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    spl3_8 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f672,plain,(
% 0.22/0.54    sK1 = sK2 | ~spl3_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f671])).
% 0.22/0.54  fof(f671,plain,(
% 0.22/0.54    spl3_28 <=> sK1 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v2_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f41])).
% 0.22/0.54  % (17430)Refutation not found, incomplete strategy% (17430)------------------------------
% 0.22/0.54  % (17430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17430)Memory used [KB]: 10618
% 0.22/0.54  % (17430)Time elapsed: 0.116 s
% 0.22/0.54  % (17430)------------------------------
% 0.22/0.54  % (17430)------------------------------
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f18])).
% 0.22/0.54  fof(f18,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.54  % (17429)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  fof(f787,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f786,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f56,f57])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(rectify,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (v1_funct_1(k1_xboole_0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.22/0.54  fof(f786,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f503,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f55,f57])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    v1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f503,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f144,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f53,f57])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f143,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(superposition,[],[f62,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.54  fof(f1075,plain,(
% 0.22/0.54    ( ! [X2,X3] : (v1_funct_2(k2_funct_1(X2),X2,X3) | ~v1_xboole_0(X2) | ~v1_xboole_0(k2_funct_1(X2))) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1040,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f54,f57])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f1040,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r1_tarski(k2_funct_1(X2),X3) | v1_funct_2(k2_funct_1(X2),X2,X3) | ~v1_xboole_0(X2) | ~v1_xboole_0(k2_funct_1(X2))) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(superposition,[],[f794,f99])).
% 0.22/0.54  fof(f794,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | v1_funct_2(k2_funct_1(X0),X0,X1) | ~v1_xboole_0(X0)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f793,f780])).
% 0.22/0.54  fof(f793,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v2_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f792,f102])).
% 0.22/0.54  fof(f792,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f532,f101])).
% 0.22/0.54  fof(f532,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(X0),X0,X1) | ~r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f160,f99])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f159,f63])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f154,f64])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ( ! [X2,X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),X2) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(superposition,[],[f71,f65])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f1116,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_funct_2(k2_funct_1(X0),X0,sK0) | ~v1_xboole_0(X0)) ) | (spl3_2 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(superposition,[],[f1115,f57])).
% 0.22/0.54  fof(f1115,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(forward_demodulation,[],[f1114,f731])).
% 0.22/0.54  fof(f1114,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_8)),
% 0.22/0.54    inference(forward_demodulation,[],[f91,f205])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.54  fof(f1103,plain,(
% 0.22/0.54    spl3_3 | ~spl3_8 | ~spl3_22 | ~spl3_28),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1102])).
% 0.22/0.54  fof(f1102,plain,(
% 0.22/0.54    $false | (spl3_3 | ~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1091,f51])).
% 0.22/0.54  fof(f1091,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | (spl3_3 | ~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.54    inference(resolution,[],[f1087,f812])).
% 0.22/0.54  fof(f812,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_xboole_0(X0)) ) | (spl3_3 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(superposition,[],[f742,f57])).
% 0.22/0.54  fof(f742,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8 | ~spl3_28)),
% 0.22/0.54    inference(backward_demodulation,[],[f697,f731])).
% 0.22/0.54  fof(f697,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8)),
% 0.22/0.54    inference(backward_demodulation,[],[f94,f205])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.54  fof(f1087,plain,(
% 0.22/0.54    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | (~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1084,f54])).
% 0.22/0.55  fof(f1084,plain,(
% 0.22/0.55    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | (~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.55    inference(backward_demodulation,[],[f766,f1081])).
% 0.22/0.55  fof(f1081,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.55    inference(forward_demodulation,[],[f1080,f205])).
% 0.22/0.55  fof(f1080,plain,(
% 0.22/0.55    sK1 = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_22 | ~spl3_28)),
% 0.22/0.55    inference(forward_demodulation,[],[f639,f731])).
% 0.22/0.55  fof(f639,plain,(
% 0.22/0.55    sK1 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f638])).
% 0.22/0.55  fof(f638,plain,(
% 0.22/0.55    spl3_22 <=> sK1 = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.55  fof(f766,plain,(
% 0.22/0.55    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.55    inference(subsumption_resolution,[],[f765,f55])).
% 0.22/0.55  fof(f765,plain,(
% 0.22/0.55    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.55    inference(subsumption_resolution,[],[f764,f56])).
% 0.22/0.55  fof(f764,plain,(
% 0.22/0.55    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_8 | ~spl3_28)),
% 0.22/0.55    inference(subsumption_resolution,[],[f611,f733])).
% 0.22/0.55  fof(f611,plain,(
% 0.22/0.55    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X2) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f181,f53])).
% 0.22/0.56  % (17422)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f180,f63])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f175,f64])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    ( ! [X2,X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),X2))) | ~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(superposition,[],[f72,f65])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f1074,plain,(
% 0.22/0.56    spl3_3 | ~spl3_8 | ~spl3_21 | ~spl3_28 | ~spl3_37),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1073])).
% 0.22/0.56  fof(f1073,plain,(
% 0.22/0.56    $false | (spl3_3 | ~spl3_8 | ~spl3_21 | ~spl3_28 | ~spl3_37)),
% 0.22/0.56    inference(subsumption_resolution,[],[f1071,f974])).
% 0.22/0.56  fof(f974,plain,(
% 0.22/0.56    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl3_37),
% 0.22/0.56    inference(avatar_component_clause,[],[f973])).
% 0.22/0.56  fof(f973,plain,(
% 0.22/0.56    spl3_37 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.56  fof(f1071,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_funct_1(k1_xboole_0)) | (spl3_3 | ~spl3_8 | ~spl3_21 | ~spl3_28)),
% 0.22/0.56    inference(resolution,[],[f1026,f100])).
% 0.22/0.56  fof(f1026,plain,(
% 0.22/0.56    ~r1_tarski(k2_funct_1(k1_xboole_0),sK0) | (spl3_3 | ~spl3_8 | ~spl3_21 | ~spl3_28)),
% 0.22/0.56    inference(resolution,[],[f853,f742])).
% 0.22/0.56  fof(f853,plain,(
% 0.22/0.56    ( ! [X2] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~r1_tarski(k2_funct_1(k1_xboole_0),X2)) ) | (~spl3_8 | ~spl3_21 | ~spl3_28)),
% 0.22/0.56    inference(backward_demodulation,[],[f766,f850])).
% 0.22/0.56  fof(f850,plain,(
% 0.22/0.56    k2_funct_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_21 | ~spl3_28)),
% 0.22/0.56    inference(forward_demodulation,[],[f636,f731])).
% 0.22/0.56  fof(f636,plain,(
% 0.22/0.56    k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f635])).
% 0.22/0.56  fof(f635,plain,(
% 0.22/0.56    spl3_21 <=> k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.56  fof(f1024,plain,(
% 0.22/0.56    spl3_38),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1023])).
% 0.22/0.56  fof(f1023,plain,(
% 0.22/0.56    $false | spl3_38),
% 0.22/0.56    inference(subsumption_resolution,[],[f1019,f51])).
% 0.22/0.56  fof(f1019,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | spl3_38),
% 0.22/0.56    inference(resolution,[],[f979,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.22/0.56  fof(f979,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | spl3_38),
% 0.22/0.56    inference(avatar_component_clause,[],[f978])).
% 0.22/0.56  fof(f978,plain,(
% 0.22/0.56    spl3_38 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.56  fof(f980,plain,(
% 0.22/0.56    spl3_37 | ~spl3_38 | ~spl3_8 | ~spl3_28 | ~spl3_33),
% 0.22/0.56    inference(avatar_split_clause,[],[f976,f896,f671,f204,f978,f973])).
% 0.22/0.56  fof(f896,plain,(
% 0.22/0.56    spl3_33 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.56  fof(f976,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl3_8 | ~spl3_28 | ~spl3_33)),
% 0.22/0.56    inference(forward_demodulation,[],[f887,f897])).
% 0.22/0.56  fof(f897,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_33),
% 0.22/0.56    inference(avatar_component_clause,[],[f896])).
% 0.22/0.56  fof(f887,plain,(
% 0.22/0.56    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0)) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(resolution,[],[f772,f58])).
% 0.22/0.56  fof(f772,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f771,f55])).
% 0.22/0.56  fof(f771,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f770,f56])).
% 0.22/0.56  fof(f770,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f522,f733])).
% 0.22/0.56  fof(f522,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0))) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f150,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f149,f63])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f147,f64])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k1_relat_1(X0)))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(superposition,[],[f62,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f934,plain,(
% 0.22/0.56    spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_32),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f933])).
% 0.22/0.56  fof(f933,plain,(
% 0.22/0.56    $false | (spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_32)),
% 0.22/0.56    inference(subsumption_resolution,[],[f917,f179])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f178,f54])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f177,f53])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f176,f55])).
% 0.22/0.56  fof(f176,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f174,f56])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.56    inference(superposition,[],[f72,f52])).
% 0.22/0.56  fof(f917,plain,(
% 0.22/0.56    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_8 | ~spl3_28 | ~spl3_32)),
% 0.22/0.56    inference(backward_demodulation,[],[f742,f894])).
% 0.22/0.56  fof(f894,plain,(
% 0.22/0.56    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_32),
% 0.22/0.56    inference(avatar_component_clause,[],[f893])).
% 0.22/0.56  fof(f893,plain,(
% 0.22/0.56    spl3_32 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.56  fof(f909,plain,(
% 0.22/0.56    spl3_32 | spl3_33 | ~spl3_8 | ~spl3_28),
% 0.22/0.56    inference(avatar_split_clause,[],[f908,f671,f204,f896,f893])).
% 0.22/0.56  fof(f908,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f907,f51])).
% 0.22/0.56  fof(f907,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f884,f778])).
% 0.22/0.56  fof(f778,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f777,f55])).
% 0.22/0.56  fof(f777,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f776,f56])).
% 0.22/0.56  fof(f776,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f438,f733])).
% 0.22/0.56  fof(f438,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f152,f52])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f151,f63])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f148,f64])).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(superposition,[],[f61,f66])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f884,plain,(
% 0.22/0.56    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl3_8 | ~spl3_28)),
% 0.22/0.56    inference(resolution,[],[f772,f183])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | X0 = X2 | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(superposition,[],[f83,f57])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.22/0.56    inference(equality_resolution,[],[f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f849,plain,(
% 0.22/0.56    ~spl3_8 | spl3_20 | ~spl3_28),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f848])).
% 0.22/0.56  fof(f848,plain,(
% 0.22/0.56    $false | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f847,f51])).
% 0.22/0.56  fof(f847,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(forward_demodulation,[],[f846,f52])).
% 0.22/0.56  fof(f846,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f845,f55])).
% 0.22/0.56  fof(f845,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f844,f56])).
% 0.22/0.56  fof(f844,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f841,f733])).
% 0.22/0.56  fof(f841,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(superposition,[],[f737,f66])).
% 0.22/0.56  fof(f737,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_relat_1(k2_funct_1(k1_xboole_0))) | (~spl3_8 | spl3_20 | ~spl3_28)),
% 0.22/0.56    inference(backward_demodulation,[],[f633,f731])).
% 0.22/0.56  fof(f633,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_relat_1(k2_funct_1(sK2))) | spl3_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f632])).
% 0.22/0.56  fof(f632,plain,(
% 0.22/0.56    spl3_20 <=> v1_xboole_0(k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.56  fof(f693,plain,(
% 0.22/0.56    spl3_7 | spl3_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f692,f204,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    spl3_7 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.56  fof(f692,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f228,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(resolution,[],[f47,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f686,plain,(
% 0.22/0.56    ~spl3_5 | spl3_28),
% 0.22/0.56    inference(avatar_split_clause,[],[f344,f671,f113])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    spl3_5 <=> v1_xboole_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.56  fof(f344,plain,(
% 0.22/0.56    sK1 = sK2 | ~v1_xboole_0(sK2)),
% 0.22/0.56    inference(superposition,[],[f99,f163])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f161,f47])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(superposition,[],[f73,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f682,plain,(
% 0.22/0.56    ~spl3_4 | spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f230,f113,f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    spl3_4 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f47,f58])).
% 0.22/0.56  fof(f656,plain,(
% 0.22/0.56    spl3_3 | ~spl3_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f655])).
% 0.22/0.56  fof(f655,plain,(
% 0.22/0.56    $false | (spl3_3 | ~spl3_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f654,f94])).
% 0.22/0.56  fof(f654,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_7),
% 0.22/0.56    inference(forward_demodulation,[],[f653,f241])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~spl3_7),
% 0.22/0.56    inference(subsumption_resolution,[],[f237,f47])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_7),
% 0.22/0.56    inference(superposition,[],[f202,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f201])).
% 0.22/0.56  fof(f653,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f652,f120])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f116,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f59,f47])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.56  fof(f652,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f651,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f651,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f628,f48])).
% 0.22/0.56  fof(f628,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f515,f66])).
% 0.22/0.56  fof(f515,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f514,f120])).
% 0.22/0.56  fof(f514,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f513,f45])).
% 0.22/0.56  fof(f513,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f506,f48])).
% 0.22/0.56  fof(f506,plain,(
% 0.22/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f144,f163])).
% 0.22/0.56  fof(f640,plain,(
% 0.22/0.56    ~spl3_20 | spl3_21 | spl3_22),
% 0.22/0.56    inference(avatar_split_clause,[],[f630,f638,f635,f632])).
% 0.22/0.56  fof(f630,plain,(
% 0.22/0.56    sK1 = k2_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_xboole_0(k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f624,f434])).
% 0.22/0.56  fof(f434,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f433,f120])).
% 0.22/0.56  fof(f433,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f432,f45])).
% 0.22/0.56  fof(f432,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f415,f48])).
% 0.22/0.56  fof(f415,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f146,f163])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f145,f63])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f142,f64])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X1] : (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(superposition,[],[f61,f65])).
% 0.22/0.56  fof(f624,plain,(
% 0.22/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | sK1 = k2_relat_1(k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_xboole_0(k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    inference(resolution,[],[f515,f183])).
% 0.22/0.56  fof(f492,plain,(
% 0.22/0.56    spl3_2 | ~spl3_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f491])).
% 0.22/0.56  fof(f491,plain,(
% 0.22/0.56    $false | (spl3_2 | ~spl3_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f490,f91])).
% 0.22/0.56  fof(f490,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl3_7),
% 0.22/0.56    inference(forward_demodulation,[],[f489,f241])).
% 0.22/0.56  fof(f489,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f488,f120])).
% 0.22/0.56  fof(f488,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f487,f45])).
% 0.22/0.56  fof(f487,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f485,f48])).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(superposition,[],[f434,f66])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    spl3_4 | ~spl3_8),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    $false | (spl3_4 | ~spl3_8)),
% 0.22/0.56    inference(subsumption_resolution,[],[f219,f51])).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | (spl3_4 | ~spl3_8)),
% 0.22/0.56    inference(backward_demodulation,[],[f130,f205])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | spl3_4),
% 0.22/0.56    inference(resolution,[],[f111,f68])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f110])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    spl3_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    $false | spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f117,f67])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f116,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.56    inference(subsumption_resolution,[],[f106,f45])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.56    inference(resolution,[],[f64,f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f50,f93,f90,f87])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (17412)------------------------------
% 0.22/0.56  % (17412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17412)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (17412)Memory used [KB]: 11001
% 0.22/0.56  % (17412)Time elapsed: 0.106 s
% 0.22/0.56  % (17412)------------------------------
% 0.22/0.56  % (17412)------------------------------
% 0.22/0.56  % (17418)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.56  % (17409)Success in time 0.195 s
%------------------------------------------------------------------------------

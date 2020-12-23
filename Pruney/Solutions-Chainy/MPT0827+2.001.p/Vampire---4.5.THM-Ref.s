%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:33 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 442 expanded)
%              Number of leaves         :   18 ( 111 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 (1069 expanded)
%              Number of equality atoms :   36 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f791,f2280])).

fof(f2280,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f2279])).

fof(f2279,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f2278,f255])).

fof(f255,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_1 ),
    inference(superposition,[],[f82,f147])).

fof(f147,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2278,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f2277,f500])).

fof(f500,plain,(
    ! [X2] : k2_relat_1(k6_relat_1(X2)) = X2 ),
    inference(subsumption_resolution,[],[f493,f271])).

fof(f271,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k6_relat_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f270,f107])).

fof(f107,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

% (27995)Refutation not found, incomplete strategy% (27995)------------------------------
% (27995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27995)Termination reason: Refutation not found, incomplete strategy

% (27995)Memory used [KB]: 6140
% (27995)Time elapsed: 0.222 s
% (27995)------------------------------
% (27995)------------------------------
fof(f270,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f128,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f128,plain,(
    ! [X0] : v5_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f76,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f493,plain,(
    ! [X2] :
      ( k2_relat_1(k6_relat_1(X2)) = X2
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X2)),X2) ) ),
    inference(resolution,[],[f400,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f400,plain,(
    ! [X1] : r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[],[f257,f258])).

fof(f258,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f70,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f257,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f107,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f2277,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f2276,f107])).

fof(f2276,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f2106,f62])).

fof(f2106,plain,(
    v5_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(superposition,[],[f1140,f1386])).

fof(f1386,plain,(
    ! [X5] : k6_relat_1(X5) = k6_relat_1(k1_relat_1(k6_relat_1(X5))) ),
    inference(forward_demodulation,[],[f1358,f288])).

fof(f288,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(resolution,[],[f145,f107])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(resolution,[],[f58,f77])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1358,plain,(
    ! [X5] : k6_relat_1(k1_relat_1(k6_relat_1(X5))) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X5))),k6_relat_1(X5)) ),
    inference(resolution,[],[f798,f269])).

fof(f269,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f268,f107])).

fof(f268,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f126,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f126,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f75,f53])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f798,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k6_relat_1(X19) = k5_relat_1(k6_relat_1(X19),k6_relat_1(X20)) ) ),
    inference(subsumption_resolution,[],[f774,f107])).

fof(f774,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k6_relat_1(X19) = k5_relat_1(k6_relat_1(X19),k6_relat_1(X20))
      | ~ v1_relat_1(k6_relat_1(X19)) ) ),
    inference(superposition,[],[f59,f500])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1140,plain,(
    v5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(sK2))),k1_relat_1(sK3)) ),
    inference(resolution,[],[f799,f136])).

fof(f136,plain,(
    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f135,f107])).

fof(f135,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f131,f106])).

fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f72,f49])).

fof(f131,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f799,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | v5_relat_1(k6_relat_1(X21),X22) ) ),
    inference(subsumption_resolution,[],[f775,f107])).

fof(f775,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | v5_relat_1(k6_relat_1(X21),X22)
      | ~ v1_relat_1(k6_relat_1(X21)) ) ),
    inference(superposition,[],[f63,f500])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f791,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f789,f256])).

fof(f256,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl4_2 ),
    inference(superposition,[],[f86,f149])).

fof(f149,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f74,f49])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f86,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f789,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f766,f500])).

fof(f766,plain,(
    r1_tarski(sK2,k2_relat_1(k6_relat_1(k2_relat_1(sK3)))) ),
    inference(superposition,[],[f490,f500])).

fof(f490,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(k6_relat_1(k2_relat_1(sK3)))) ),
    inference(superposition,[],[f257,f318])).

fof(f318,plain,(
    k2_relat_1(k6_relat_1(sK2)) = k9_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_relat_1(k6_relat_1(sK2))) ),
    inference(resolution,[],[f225,f65])).

fof(f225,plain,(
    m1_subset_1(k2_relat_1(k6_relat_1(sK2)),k1_zfmisc_1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f144,f70])).

fof(f144,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f143,f107])).

fof(f143,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f139,f106])).

fof(f139,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f84,f80])).

fof(f51,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:01:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (27989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.49  % (28001)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (27987)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (28002)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (28011)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (27995)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (28006)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (28009)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (27993)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (27987)Refutation not found, incomplete strategy% (27987)------------------------------
% 0.22/0.51  % (27987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27987)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27987)Memory used [KB]: 10618
% 0.22/0.51  % (27987)Time elapsed: 0.084 s
% 0.22/0.51  % (27987)------------------------------
% 0.22/0.51  % (27987)------------------------------
% 0.22/0.51  % (27997)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28007)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (27988)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (27990)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (27986)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (27994)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (27986)Refutation not found, incomplete strategy% (27986)------------------------------
% 0.22/0.52  % (27986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27986)Memory used [KB]: 10618
% 0.22/0.52  % (27986)Time elapsed: 0.106 s
% 0.22/0.52  % (27986)------------------------------
% 0.22/0.52  % (27986)------------------------------
% 0.22/0.52  % (27998)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (28000)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (28013)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (28000)Refutation not found, incomplete strategy% (28000)------------------------------
% 0.22/0.53  % (28000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28000)Memory used [KB]: 6268
% 0.22/0.53  % (28000)Time elapsed: 0.119 s
% 0.22/0.53  % (28000)------------------------------
% 0.22/0.53  % (28000)------------------------------
% 0.22/0.53  % (27999)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (28010)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (28012)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (28004)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (27991)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (27992)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (28003)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (27991)Refutation not found, incomplete strategy% (27991)------------------------------
% 0.22/0.54  % (27991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27991)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27991)Memory used [KB]: 6140
% 0.22/0.54  % (27991)Time elapsed: 0.141 s
% 0.22/0.54  % (27991)------------------------------
% 0.22/0.54  % (27991)------------------------------
% 0.22/0.55  % (27992)Refutation not found, incomplete strategy% (27992)------------------------------
% 0.22/0.55  % (27992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27992)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27992)Memory used [KB]: 10618
% 0.22/0.55  % (27992)Time elapsed: 0.136 s
% 0.22/0.55  % (27992)------------------------------
% 0.22/0.55  % (27992)------------------------------
% 0.22/0.55  % (28008)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.80/0.63  % (27997)Refutation found. Thanks to Tanya!
% 1.80/0.63  % SZS status Theorem for theBenchmark
% 1.80/0.63  % SZS output start Proof for theBenchmark
% 1.80/0.63  fof(f2281,plain,(
% 1.80/0.63    $false),
% 1.80/0.63    inference(avatar_sat_refutation,[],[f87,f791,f2280])).
% 1.80/0.63  fof(f2280,plain,(
% 1.80/0.63    spl4_1),
% 1.80/0.63    inference(avatar_contradiction_clause,[],[f2279])).
% 1.80/0.63  fof(f2279,plain,(
% 1.80/0.63    $false | spl4_1),
% 1.80/0.63    inference(subsumption_resolution,[],[f2278,f255])).
% 1.80/0.63  fof(f255,plain,(
% 1.80/0.63    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_1),
% 1.80/0.63    inference(superposition,[],[f82,f147])).
% 1.80/0.63  fof(f147,plain,(
% 1.80/0.63    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.80/0.63    inference(resolution,[],[f73,f49])).
% 1.80/0.63  fof(f49,plain,(
% 1.80/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.80/0.63    inference(cnf_transformation,[],[f43])).
% 1.80/0.63  fof(f43,plain,(
% 1.80/0.63    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f42])).
% 1.80/0.63  fof(f42,plain,(
% 1.80/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f24,plain,(
% 1.80/0.63    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.63    inference(flattening,[],[f23])).
% 1.80/0.63  fof(f23,plain,(
% 1.80/0.63    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.63    inference(ennf_transformation,[],[f21])).
% 1.80/0.63  fof(f21,negated_conjecture,(
% 1.80/0.63    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.80/0.63    inference(negated_conjecture,[],[f20])).
% 1.80/0.63  fof(f20,conjecture,(
% 1.80/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.80/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 1.80/0.63  fof(f73,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f39])).
% 1.80/0.63  fof(f39,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.63    inference(ennf_transformation,[],[f17])).
% 1.80/0.63  fof(f17,axiom,(
% 1.80/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.80/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.80/0.63  fof(f82,plain,(
% 1.80/0.63    ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) | spl4_1),
% 1.80/0.63    inference(avatar_component_clause,[],[f80])).
% 1.80/0.63  fof(f80,plain,(
% 1.80/0.63    spl4_1 <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.80/0.63  fof(f2278,plain,(
% 1.80/0.63    r1_tarski(sK2,k1_relat_1(sK3))),
% 1.80/0.63    inference(forward_demodulation,[],[f2277,f500])).
% 1.80/0.63  fof(f500,plain,(
% 1.80/0.63    ( ! [X2] : (k2_relat_1(k6_relat_1(X2)) = X2) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f493,f271])).
% 1.80/0.63  fof(f271,plain,(
% 1.80/0.63    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f270,f107])).
% 1.80/0.63  fof(f107,plain,(
% 1.80/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.80/0.63    inference(resolution,[],[f72,f53])).
% 1.80/0.63  fof(f53,plain,(
% 1.80/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.80/0.63    inference(cnf_transformation,[],[f19])).
% 1.80/0.63  fof(f19,axiom,(
% 1.80/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.80/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.80/0.63  fof(f72,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f38])).
% 1.80/0.63  fof(f38,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.80/0.63    inference(ennf_transformation,[],[f15])).
% 1.80/0.63  fof(f15,axiom,(
% 1.80/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.80/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.12/0.64  % (27995)Refutation not found, incomplete strategy% (27995)------------------------------
% 2.12/0.64  % (27995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (27995)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.64  
% 2.12/0.64  % (27995)Memory used [KB]: 6140
% 2.12/0.64  % (27995)Time elapsed: 0.222 s
% 2.12/0.64  % (27995)------------------------------
% 2.12/0.64  % (27995)------------------------------
% 2.23/0.64  fof(f270,plain,(
% 2.23/0.64    ( ! [X0] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.23/0.64    inference(resolution,[],[f128,f62])).
% 2.23/0.64  fof(f62,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f45])).
% 2.23/0.64  fof(f45,plain,(
% 2.23/0.64    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(nnf_transformation,[],[f34])).
% 2.23/0.64  fof(f34,plain,(
% 2.23/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f9])).
% 2.23/0.64  fof(f9,axiom,(
% 2.23/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.23/0.64  fof(f128,plain,(
% 2.23/0.64    ( ! [X0] : (v5_relat_1(k6_relat_1(X0),X0)) )),
% 2.23/0.64    inference(resolution,[],[f76,f53])).
% 2.23/0.64  fof(f76,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f41])).
% 2.23/0.64  fof(f41,plain,(
% 2.23/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.64    inference(ennf_transformation,[],[f16])).
% 2.23/0.64  fof(f16,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.23/0.64  fof(f493,plain,(
% 2.23/0.64    ( ! [X2] : (k2_relat_1(k6_relat_1(X2)) = X2 | ~r1_tarski(k2_relat_1(k6_relat_1(X2)),X2)) )),
% 2.23/0.64    inference(resolution,[],[f400,f68])).
% 2.23/0.64  fof(f68,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f47])).
% 2.23/0.64  fof(f47,plain,(
% 2.23/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/0.64    inference(flattening,[],[f46])).
% 2.23/0.64  fof(f46,plain,(
% 2.23/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.23/0.64    inference(nnf_transformation,[],[f2])).
% 2.23/0.64  fof(f2,axiom,(
% 2.23/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.23/0.64  fof(f400,plain,(
% 2.23/0.64    ( ! [X1] : (r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))) )),
% 2.23/0.64    inference(superposition,[],[f257,f258])).
% 2.23/0.64  fof(f258,plain,(
% 2.23/0.64    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.23/0.64    inference(resolution,[],[f91,f65])).
% 2.23/0.64  fof(f65,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 2.23/0.64    inference(cnf_transformation,[],[f36])).
% 2.23/0.64  fof(f36,plain,(
% 2.23/0.64    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.23/0.64    inference(ennf_transformation,[],[f14])).
% 2.23/0.64  fof(f14,axiom,(
% 2.23/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 2.23/0.64  fof(f91,plain,(
% 2.23/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.23/0.64    inference(resolution,[],[f70,f77])).
% 2.23/0.64  fof(f77,plain,(
% 2.23/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.23/0.64    inference(equality_resolution,[],[f67])).
% 2.23/0.64  fof(f67,plain,(
% 2.23/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.23/0.64    inference(cnf_transformation,[],[f47])).
% 2.23/0.64  fof(f70,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f48])).
% 2.23/0.64  fof(f48,plain,(
% 2.23/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.23/0.64    inference(nnf_transformation,[],[f6])).
% 2.23/0.64  fof(f6,axiom,(
% 2.23/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.23/0.64  fof(f257,plain,(
% 2.23/0.64    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),k2_relat_1(k6_relat_1(X0)))) )),
% 2.23/0.64    inference(resolution,[],[f107,f57])).
% 2.23/0.64  fof(f57,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 2.23/0.64    inference(cnf_transformation,[],[f28])).
% 2.23/0.64  fof(f28,plain,(
% 2.23/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f10])).
% 2.23/0.64  fof(f10,axiom,(
% 2.23/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 2.23/0.64  fof(f2277,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))),
% 2.23/0.64    inference(subsumption_resolution,[],[f2276,f107])).
% 2.23/0.64  fof(f2276,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK2))),
% 2.23/0.64    inference(resolution,[],[f2106,f62])).
% 2.23/0.64  fof(f2106,plain,(
% 2.23/0.64    v5_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))),
% 2.23/0.64    inference(superposition,[],[f1140,f1386])).
% 2.23/0.64  fof(f1386,plain,(
% 2.23/0.64    ( ! [X5] : (k6_relat_1(X5) = k6_relat_1(k1_relat_1(k6_relat_1(X5)))) )),
% 2.23/0.64    inference(forward_demodulation,[],[f1358,f288])).
% 2.23/0.64  fof(f288,plain,(
% 2.23/0.64    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) )),
% 2.23/0.64    inference(resolution,[],[f145,f107])).
% 2.23/0.64  fof(f145,plain,(
% 2.23/0.64    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.23/0.64    inference(resolution,[],[f58,f77])).
% 2.23/0.64  fof(f58,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f30])).
% 2.23/0.64  fof(f30,plain,(
% 2.23/0.64    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(flattening,[],[f29])).
% 2.23/0.64  fof(f29,plain,(
% 2.23/0.64    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f12])).
% 2.23/0.64  fof(f12,axiom,(
% 2.23/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 2.23/0.64  fof(f1358,plain,(
% 2.23/0.64    ( ! [X5] : (k6_relat_1(k1_relat_1(k6_relat_1(X5))) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X5))),k6_relat_1(X5))) )),
% 2.23/0.64    inference(resolution,[],[f798,f269])).
% 2.23/0.64  fof(f269,plain,(
% 2.23/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)) )),
% 2.23/0.64    inference(subsumption_resolution,[],[f268,f107])).
% 2.23/0.64  fof(f268,plain,(
% 2.23/0.64    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.23/0.64    inference(resolution,[],[f126,f60])).
% 2.23/0.64  fof(f60,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f44])).
% 2.23/0.64  fof(f44,plain,(
% 2.23/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(nnf_transformation,[],[f33])).
% 2.23/0.64  fof(f33,plain,(
% 2.23/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f8])).
% 2.23/0.64  fof(f8,axiom,(
% 2.23/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.23/0.64  fof(f126,plain,(
% 2.23/0.64    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 2.23/0.64    inference(resolution,[],[f75,f53])).
% 2.23/0.64  fof(f75,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f41])).
% 2.23/0.64  fof(f798,plain,(
% 2.23/0.64    ( ! [X19,X20] : (~r1_tarski(X19,X20) | k6_relat_1(X19) = k5_relat_1(k6_relat_1(X19),k6_relat_1(X20))) )),
% 2.23/0.64    inference(subsumption_resolution,[],[f774,f107])).
% 2.23/0.64  fof(f774,plain,(
% 2.23/0.64    ( ! [X19,X20] : (~r1_tarski(X19,X20) | k6_relat_1(X19) = k5_relat_1(k6_relat_1(X19),k6_relat_1(X20)) | ~v1_relat_1(k6_relat_1(X19))) )),
% 2.23/0.64    inference(superposition,[],[f59,f500])).
% 2.23/0.64  fof(f59,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f32])).
% 2.23/0.64  fof(f32,plain,(
% 2.23/0.64    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(flattening,[],[f31])).
% 2.23/0.64  fof(f31,plain,(
% 2.23/0.64    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.23/0.64    inference(ennf_transformation,[],[f13])).
% 2.23/0.64  fof(f13,axiom,(
% 2.23/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.23/0.64  fof(f1140,plain,(
% 2.23/0.64    v5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(sK2))),k1_relat_1(sK3))),
% 2.23/0.64    inference(resolution,[],[f799,f136])).
% 2.23/0.64  fof(f136,plain,(
% 2.23/0.64    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3))),
% 2.23/0.64    inference(subsumption_resolution,[],[f135,f107])).
% 2.23/0.64  fof(f135,plain,(
% 2.23/0.64    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK2))),
% 2.23/0.64    inference(subsumption_resolution,[],[f131,f106])).
% 2.23/0.64  fof(f106,plain,(
% 2.23/0.64    v1_relat_1(sK3)),
% 2.23/0.64    inference(resolution,[],[f72,f49])).
% 2.23/0.64  fof(f131,plain,(
% 2.23/0.64    r1_tarski(k1_relat_1(k6_relat_1(sK2)),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2))),
% 2.23/0.64    inference(resolution,[],[f54,f50])).
% 2.23/0.64  fof(f50,plain,(
% 2.23/0.64    r1_tarski(k6_relat_1(sK2),sK3)),
% 2.23/0.64    inference(cnf_transformation,[],[f43])).
% 2.23/0.64  fof(f54,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f26])).
% 2.23/0.64  fof(f26,plain,(
% 2.23/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.64    inference(flattening,[],[f25])).
% 2.23/0.64  fof(f25,plain,(
% 2.23/0.64    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.23/0.64    inference(ennf_transformation,[],[f11])).
% 2.23/0.64  fof(f11,axiom,(
% 2.23/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 2.23/0.64  fof(f799,plain,(
% 2.23/0.64    ( ! [X21,X22] : (~r1_tarski(X21,X22) | v5_relat_1(k6_relat_1(X21),X22)) )),
% 2.23/0.64    inference(subsumption_resolution,[],[f775,f107])).
% 2.23/0.64  fof(f775,plain,(
% 2.23/0.64    ( ! [X21,X22] : (~r1_tarski(X21,X22) | v5_relat_1(k6_relat_1(X21),X22) | ~v1_relat_1(k6_relat_1(X21))) )),
% 2.23/0.64    inference(superposition,[],[f63,f500])).
% 2.23/0.64  fof(f63,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f45])).
% 2.23/0.64  fof(f791,plain,(
% 2.23/0.64    spl4_2),
% 2.23/0.64    inference(avatar_contradiction_clause,[],[f790])).
% 2.23/0.64  fof(f790,plain,(
% 2.23/0.64    $false | spl4_2),
% 2.23/0.64    inference(subsumption_resolution,[],[f789,f256])).
% 2.23/0.64  fof(f256,plain,(
% 2.23/0.64    ~r1_tarski(sK2,k2_relat_1(sK3)) | spl4_2),
% 2.23/0.64    inference(superposition,[],[f86,f149])).
% 2.23/0.64  fof(f149,plain,(
% 2.23/0.64    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 2.23/0.64    inference(resolution,[],[f74,f49])).
% 2.23/0.64  fof(f74,plain,(
% 2.23/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f40])).
% 2.23/0.64  fof(f40,plain,(
% 2.23/0.64    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.23/0.64    inference(ennf_transformation,[],[f18])).
% 2.23/0.64  fof(f18,axiom,(
% 2.23/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.23/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.23/0.64  fof(f86,plain,(
% 2.23/0.64    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | spl4_2),
% 2.23/0.64    inference(avatar_component_clause,[],[f84])).
% 2.23/0.64  fof(f84,plain,(
% 2.23/0.64    spl4_2 <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 2.23/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.23/0.64  fof(f789,plain,(
% 2.23/0.64    r1_tarski(sK2,k2_relat_1(sK3))),
% 2.23/0.64    inference(forward_demodulation,[],[f766,f500])).
% 2.23/0.64  fof(f766,plain,(
% 2.23/0.64    r1_tarski(sK2,k2_relat_1(k6_relat_1(k2_relat_1(sK3))))),
% 2.23/0.64    inference(superposition,[],[f490,f500])).
% 2.23/0.64  fof(f490,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(k6_relat_1(k2_relat_1(sK3))))),
% 2.23/0.64    inference(superposition,[],[f257,f318])).
% 2.23/0.64  fof(f318,plain,(
% 2.23/0.64    k2_relat_1(k6_relat_1(sK2)) = k9_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_relat_1(k6_relat_1(sK2)))),
% 2.23/0.64    inference(resolution,[],[f225,f65])).
% 2.23/0.64  fof(f225,plain,(
% 2.23/0.64    m1_subset_1(k2_relat_1(k6_relat_1(sK2)),k1_zfmisc_1(k2_relat_1(sK3)))),
% 2.23/0.64    inference(resolution,[],[f144,f70])).
% 2.23/0.64  fof(f144,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))),
% 2.23/0.64    inference(subsumption_resolution,[],[f143,f107])).
% 2.23/0.64  fof(f143,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK2))),
% 2.23/0.64    inference(subsumption_resolution,[],[f139,f106])).
% 2.23/0.64  fof(f139,plain,(
% 2.23/0.64    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2))),
% 2.23/0.64    inference(resolution,[],[f55,f50])).
% 2.23/0.64  fof(f55,plain,(
% 2.23/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.23/0.64    inference(cnf_transformation,[],[f26])).
% 2.23/0.64  fof(f87,plain,(
% 2.23/0.64    ~spl4_1 | ~spl4_2),
% 2.23/0.64    inference(avatar_split_clause,[],[f51,f84,f80])).
% 2.23/0.64  fof(f51,plain,(
% 2.23/0.64    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 2.23/0.64    inference(cnf_transformation,[],[f43])).
% 2.23/0.64  % SZS output end Proof for theBenchmark
% 2.23/0.64  % (27997)------------------------------
% 2.23/0.64  % (27997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.64  % (27997)Termination reason: Refutation
% 2.23/0.64  
% 2.23/0.64  % (27997)Memory used [KB]: 12281
% 2.23/0.64  % (27997)Time elapsed: 0.217 s
% 2.23/0.64  % (27997)------------------------------
% 2.23/0.64  % (27997)------------------------------
% 2.23/0.65  % (27983)Success in time 0.284 s
%------------------------------------------------------------------------------

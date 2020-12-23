%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:41 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 444 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  239 (1421 expanded)
%              Number of equality atoms :   97 ( 443 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f636,plain,(
    $false ),
    inference(subsumption_resolution,[],[f635,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f635,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f113,f632])).

fof(f632,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f631,f281])).

fof(f281,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f150,f278])).

fof(f278,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f276,f150])).

fof(f276,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f270])).

fof(f270,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f95,f188])).

fof(f188,plain,(
    ! [X3] :
      ( k1_relat_1(k1_xboole_0) = k1_tarski(X3)
      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f150,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
      | k1_tarski(X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f66,f80])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f150,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k1_xboole_0),X2) ),
    inference(subsumption_resolution,[],[f149,f83])).

fof(f83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f57,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

% (21685)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f149,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X2)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f121,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f121,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f99,f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f71,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f75,f81])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f631,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0))
      | k1_xboole_0 = k9_relat_1(sK3,X0) ) ),
    inference(forward_demodulation,[],[f628,f622])).

fof(f622,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f601])).

fof(f601,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f143,f594])).

fof(f594,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f580,f145])).

fof(f145,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f122,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (21693)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (21685)Refutation not found, incomplete strategy% (21685)------------------------------
% (21685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21685)Termination reason: Refutation not found, incomplete strategy

% (21685)Memory used [KB]: 1663
% (21685)Time elapsed: 0.135 s
% (21685)------------------------------
% (21685)------------------------------
fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f54,f57])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f580,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f113,f406])).

fof(f406,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(equality_resolution,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | k1_xboole_0 = k1_relat_1(sK3) ) ),
    inference(superposition,[],[f140,f160])).

fof(f160,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f139,f67])).

fof(f139,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(resolution,[],[f122,f115])).

fof(f115,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(resolution,[],[f98,f60])).

fof(f98,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(resolution,[],[f75,f48])).

fof(f140,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) ) ),
    inference(resolution,[],[f122,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))
      | k1_tarski(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f143,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f122,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f628,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(sK3,X0)
      | ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) ) ),
    inference(backward_demodulation,[],[f175,f622])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))
      | k2_relat_1(sK3) = k9_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f145,f66])).

fof(f113,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f50,f110])).

fof(f110,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

% (21702)Refutation not found, incomplete strategy% (21702)------------------------------
% (21702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21703)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (21702)Termination reason: Refutation not found, incomplete strategy

% (21702)Memory used [KB]: 1791
% (21702)Time elapsed: 0.120 s
% (21702)------------------------------
% (21702)------------------------------
% (21699)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (21694)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (21703)Refutation not found, incomplete strategy% (21703)------------------------------
% (21703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21703)Termination reason: Refutation not found, incomplete strategy

% (21703)Memory used [KB]: 1791
% (21703)Time elapsed: 0.137 s
% (21703)------------------------------
% (21703)------------------------------
% (21713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (21699)Refutation not found, incomplete strategy% (21699)------------------------------
% (21699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21699)Termination reason: Refutation not found, incomplete strategy

% (21699)Memory used [KB]: 1791
% (21699)Time elapsed: 0.138 s
% (21699)------------------------------
% (21699)------------------------------
% (21711)Refutation not found, incomplete strategy% (21711)------------------------------
% (21711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f50,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (21687)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.49  % (21696)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.49  % (21704)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.50  % (21690)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (21708)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.51  % (21707)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (21692)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (21686)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.52  % (21712)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (21700)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (21702)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.52  % (21712)Refutation not found, incomplete strategy% (21712)------------------------------
% 0.19/0.52  % (21712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (21712)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (21712)Memory used [KB]: 6268
% 0.19/0.52  % (21712)Time elapsed: 0.089 s
% 0.19/0.52  % (21712)------------------------------
% 0.19/0.52  % (21712)------------------------------
% 0.19/0.53  % (21706)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.53  % (21714)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.53  % (21698)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.53  % (21714)Refutation not found, incomplete strategy% (21714)------------------------------
% 0.19/0.53  % (21714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (21714)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (21714)Memory used [KB]: 1663
% 0.19/0.53  % (21714)Time elapsed: 0.131 s
% 0.19/0.53  % (21714)------------------------------
% 0.19/0.53  % (21714)------------------------------
% 0.19/0.53  % (21691)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (21684)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (21695)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.53  % (21701)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (21697)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.54  % (21711)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (21709)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.54  % (21689)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.54  % (21692)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f636,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(subsumption_resolution,[],[f635,f80])).
% 1.39/0.54  fof(f80,plain,(
% 1.39/0.54    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.39/0.54    inference(equality_resolution,[],[f68])).
% 1.39/0.54  fof(f68,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.39/0.54    inference(flattening,[],[f42])).
% 1.39/0.54  fof(f42,plain,(
% 1.39/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.39/0.54    inference(nnf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.39/0.54  fof(f635,plain,(
% 1.39/0.54    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.54    inference(backward_demodulation,[],[f113,f632])).
% 1.39/0.54  fof(f632,plain,(
% 1.39/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f631,f281])).
% 1.39/0.54  fof(f281,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.39/0.54    inference(backward_demodulation,[],[f150,f278])).
% 1.39/0.54  fof(f278,plain,(
% 1.39/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(subsumption_resolution,[],[f276,f150])).
% 1.39/0.54  fof(f276,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f270])).
% 1.39/0.54  fof(f270,plain,(
% 1.39/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(superposition,[],[f95,f188])).
% 1.39/0.54  fof(f188,plain,(
% 1.39/0.54    ( ! [X3] : (k1_relat_1(k1_xboole_0) = k1_tarski(X3) | k1_xboole_0 = k1_relat_1(k1_xboole_0)) )),
% 1.39/0.54    inference(resolution,[],[f150,f67])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f43])).
% 1.39/0.54  fof(f95,plain,(
% 1.39/0.54    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0) | k1_tarski(X1) = k1_xboole_0) )),
% 1.39/0.54    inference(resolution,[],[f66,f80])).
% 1.39/0.54  fof(f66,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f41])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.54    inference(flattening,[],[f40])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.54    inference(nnf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f150,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(k1_relat_1(k1_xboole_0),X2)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f149,f83])).
% 1.39/0.54  fof(f83,plain,(
% 1.39/0.54    v1_relat_1(k1_xboole_0)),
% 1.39/0.54    inference(superposition,[],[f57,f81])).
% 1.39/0.54  fof(f81,plain,(
% 1.39/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.54    inference(equality_resolution,[],[f74])).
% 1.39/0.54  fof(f74,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.54    inference(flattening,[],[f45])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.54    inference(nnf_transformation,[],[f5])).
% 1.39/0.54  % (21685)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f10])).
% 1.39/0.54  fof(f10,axiom,(
% 1.39/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.54  fof(f149,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(k1_relat_1(k1_xboole_0),X2) | ~v1_relat_1(k1_xboole_0)) )),
% 1.39/0.54    inference(resolution,[],[f121,f60])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(nnf_transformation,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.39/0.54  fof(f121,plain,(
% 1.39/0.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.39/0.54    inference(resolution,[],[f99,f86])).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.39/0.54    inference(resolution,[],[f71,f77])).
% 1.39/0.54  fof(f77,plain,(
% 1.39/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.54    inference(equality_resolution,[],[f65])).
% 1.39/0.54  fof(f65,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f41])).
% 1.39/0.54  fof(f71,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.54    inference(nnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.54  fof(f99,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.39/0.54    inference(superposition,[],[f75,f81])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f34])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.39/0.54    inference(pure_predicate_removal,[],[f14])).
% 1.39/0.54  fof(f14,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.54  fof(f631,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(sK3,X0)) | k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.39/0.54    inference(forward_demodulation,[],[f628,f622])).
% 1.39/0.54  fof(f622,plain,(
% 1.39/0.54    k1_xboole_0 = k2_relat_1(sK3)),
% 1.39/0.54    inference(trivial_inequality_removal,[],[f601])).
% 1.39/0.54  fof(f601,plain,(
% 1.39/0.54    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3)),
% 1.39/0.54    inference(backward_demodulation,[],[f143,f594])).
% 1.39/0.54  fof(f594,plain,(
% 1.39/0.54    k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(subsumption_resolution,[],[f580,f145])).
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(sK3,X2),k2_relat_1(sK3))) )),
% 1.39/0.54    inference(resolution,[],[f122,f59])).
% 1.39/0.54  fof(f59,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.39/0.54  fof(f122,plain,(
% 1.39/0.54    v1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f88,f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.39/0.54    inference(cnf_transformation,[],[f37])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  % (21693)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (21685)Refutation not found, incomplete strategy% (21685)------------------------------
% 1.39/0.54  % (21685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (21685)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (21685)Memory used [KB]: 1663
% 1.39/0.54  % (21685)Time elapsed: 0.135 s
% 1.39/0.54  % (21685)------------------------------
% 1.39/0.54  % (21685)------------------------------
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.39/0.54    inference(flattening,[],[f22])).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.39/0.54    inference(ennf_transformation,[],[f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.54    inference(pure_predicate_removal,[],[f18])).
% 1.39/0.54  fof(f18,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.54    inference(negated_conjecture,[],[f17])).
% 1.39/0.54  fof(f17,conjecture,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.39/0.54  fof(f88,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.39/0.54    inference(resolution,[],[f54,f57])).
% 1.39/0.54  fof(f54,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.54  fof(f580,plain,(
% 1.39/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(superposition,[],[f113,f406])).
% 1.39/0.54  fof(f406,plain,(
% 1.39/0.54    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(equality_resolution,[],[f218])).
% 1.39/0.54  fof(f218,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | k1_xboole_0 = k1_relat_1(sK3)) )),
% 1.39/0.54    inference(superposition,[],[f140,f160])).
% 1.39/0.54  fof(f160,plain,(
% 1.39/0.54    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f139,f67])).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.39/0.54    inference(resolution,[],[f122,f115])).
% 1.39/0.54  fof(f115,plain,(
% 1.39/0.54    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.39/0.54    inference(resolution,[],[f98,f60])).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    v4_relat_1(sK3,k1_tarski(sK0))),
% 1.39/0.54    inference(resolution,[],[f75,f48])).
% 1.39/0.54  fof(f140,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) )),
% 1.39/0.54    inference(resolution,[],[f122,f116])).
% 1.39/0.54  fof(f116,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) | k1_tarski(X0) != k1_relat_1(sK3)) )),
% 1.39/0.54    inference(resolution,[],[f62,f47])).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    v1_funct_1(sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f37])).
% 1.39/0.54  fof(f62,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f31])).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(flattening,[],[f30])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,axiom,(
% 1.39/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.39/0.54    inference(resolution,[],[f122,f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f38])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(nnf_transformation,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f12])).
% 1.39/0.54  fof(f12,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.39/0.54  fof(f628,plain,(
% 1.39/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0) | ~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))) )),
% 1.39/0.54    inference(backward_demodulation,[],[f175,f622])).
% 1.39/0.54  fof(f175,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) | k2_relat_1(sK3) = k9_relat_1(sK3,X0)) )),
% 1.39/0.54    inference(resolution,[],[f145,f66])).
% 1.39/0.54  fof(f113,plain,(
% 1.39/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.54    inference(backward_demodulation,[],[f50,f110])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.39/0.54    inference(resolution,[],[f76,f48])).
% 1.39/0.54  fof(f76,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(ennf_transformation,[],[f15])).
% 1.39/0.54  % (21702)Refutation not found, incomplete strategy% (21702)------------------------------
% 1.39/0.54  % (21702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (21703)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (21702)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (21702)Memory used [KB]: 1791
% 1.39/0.54  % (21702)Time elapsed: 0.120 s
% 1.39/0.54  % (21702)------------------------------
% 1.39/0.54  % (21702)------------------------------
% 1.39/0.54  % (21699)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.54  % (21694)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (21703)Refutation not found, incomplete strategy% (21703)------------------------------
% 1.39/0.55  % (21703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (21703)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (21703)Memory used [KB]: 1791
% 1.39/0.55  % (21703)Time elapsed: 0.137 s
% 1.39/0.55  % (21703)------------------------------
% 1.39/0.55  % (21703)------------------------------
% 1.39/0.55  % (21713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.55  % (21699)Refutation not found, incomplete strategy% (21699)------------------------------
% 1.39/0.55  % (21699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (21699)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (21699)Memory used [KB]: 1791
% 1.39/0.55  % (21699)Time elapsed: 0.138 s
% 1.39/0.55  % (21699)------------------------------
% 1.39/0.55  % (21699)------------------------------
% 1.39/0.55  % (21711)Refutation not found, incomplete strategy% (21711)------------------------------
% 1.39/0.55  % (21711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  fof(f15,axiom,(
% 1.39/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.39/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (21692)------------------------------
% 1.39/0.55  % (21692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (21692)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (21692)Memory used [KB]: 2046
% 1.39/0.55  % (21692)Time elapsed: 0.090 s
% 1.39/0.55  % (21692)------------------------------
% 1.39/0.55  % (21692)------------------------------
% 1.39/0.55  % (21683)Success in time 0.192 s
%------------------------------------------------------------------------------

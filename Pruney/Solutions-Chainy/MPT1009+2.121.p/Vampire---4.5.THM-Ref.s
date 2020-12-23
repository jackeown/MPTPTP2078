%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:43 EST 2020

% Result     : Theorem 2.27s
% Output     : Refutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 468 expanded)
%              Number of leaves         :   23 ( 128 expanded)
%              Depth                    :   21
%              Number of atoms          :  267 (1541 expanded)
%              Number of equality atoms :   70 ( 292 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1034,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f638,f1033])).

fof(f1033,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f1031,f181])).

% (5216)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
fof(f181,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f172,f138])).

fof(f138,plain,(
    ! [X0] : k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f127,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f127,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f71,f59,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f172,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f127,f137,f161,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f161,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f127,f145,f70])).

fof(f145,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f137,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f137,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1031,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f1023,f123])).

fof(f123,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f59,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f1023,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1 ),
    inference(superposition,[],[f61,f692])).

fof(f692,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f127,f57,f688,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f688,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f142,f640,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f640,plain,
    ( r1_tarski(k1_tarski(sK0),k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f254,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f254,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f142,plain,(
    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f127,f124,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f124,plain,(
    v4_relat_1(sK3,k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f59,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f638,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f636,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f636,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f327,f479])).

fof(f479,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f64,f345,f83])).

fof(f345,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | spl4_1 ),
    inference(forward_demodulation,[],[f324,f63])).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f324,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
    | spl4_1 ),
    inference(superposition,[],[f181,f295])).

fof(f295,plain,
    ( k1_xboole_0 = sK3
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f64,f281,f83])).

fof(f281,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | spl4_1 ),
    inference(forward_demodulation,[],[f264,f104])).

fof(f104,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f264,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | spl4_1 ),
    inference(superposition,[],[f128,f263])).

fof(f263,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | spl4_1 ),
    inference(forward_demodulation,[],[f261,f250])).

fof(f250,plain,(
    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f249,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f249,plain,(
    k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0)) = k5_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(superposition,[],[f73,f149])).

fof(f149,plain,(
    k1_relat_1(sK3) = k3_xboole_0(k1_relat_1(sK3),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f142,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f261,plain,
    ( k1_relat_1(sK3) = k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f255,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f255,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f253])).

fof(f128,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    inference(unit_resulting_resolution,[],[f127,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f327,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f225,f295])).

fof(f225,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(unit_resulting_resolution,[],[f155,f85])).

fof(f155,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) ),
    inference(forward_demodulation,[],[f154,f123])).

fof(f154,plain,(
    ~ m1_subset_1(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0)))) ),
    inference(unit_resulting_resolution,[],[f61,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (5195)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (5206)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (5184)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (5182)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (5183)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.52  % (5185)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.52  % (5187)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (5200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.53  % (5202)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.53  % (5190)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.53  % (5191)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.53  % (5194)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (5190)Refutation not found, incomplete strategy% (5190)------------------------------
% 1.23/0.53  % (5190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (5192)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.53  % (5199)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.23/0.54  % (5209)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.54  % (5209)Refutation not found, incomplete strategy% (5209)------------------------------
% 1.38/0.54  % (5209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5209)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5209)Memory used [KB]: 1663
% 1.38/0.54  % (5209)Time elapsed: 0.124 s
% 1.38/0.54  % (5209)------------------------------
% 1.38/0.54  % (5209)------------------------------
% 1.38/0.54  % (5203)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (5204)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.54  % (5198)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.54  % (5198)Refutation not found, incomplete strategy% (5198)------------------------------
% 1.38/0.54  % (5198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5198)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5198)Memory used [KB]: 1663
% 1.38/0.54  % (5198)Time elapsed: 0.095 s
% 1.38/0.54  % (5198)------------------------------
% 1.38/0.54  % (5198)------------------------------
% 1.38/0.54  % (5204)Refutation not found, incomplete strategy% (5204)------------------------------
% 1.38/0.54  % (5204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5204)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5204)Memory used [KB]: 10746
% 1.38/0.54  % (5204)Time elapsed: 0.126 s
% 1.38/0.54  % (5204)------------------------------
% 1.38/0.54  % (5204)------------------------------
% 1.38/0.54  % (5186)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (5180)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.54  % (5193)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.54  % (5190)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5190)Memory used [KB]: 10746
% 1.38/0.54  % (5190)Time elapsed: 0.116 s
% 1.38/0.54  % (5190)------------------------------
% 1.38/0.54  % (5190)------------------------------
% 1.38/0.55  % (5208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (5181)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.55  % (5201)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (5208)Refutation not found, incomplete strategy% (5208)------------------------------
% 1.38/0.55  % (5208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5208)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5208)Memory used [KB]: 10874
% 1.38/0.55  % (5208)Time elapsed: 0.142 s
% 1.38/0.55  % (5208)------------------------------
% 1.38/0.55  % (5208)------------------------------
% 1.38/0.55  % (5207)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.55  % (5207)Refutation not found, incomplete strategy% (5207)------------------------------
% 1.38/0.55  % (5207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5207)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5207)Memory used [KB]: 6268
% 1.38/0.55  % (5207)Time elapsed: 0.137 s
% 1.38/0.55  % (5207)------------------------------
% 1.38/0.55  % (5207)------------------------------
% 1.38/0.55  % (5205)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (5196)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (5196)Refutation not found, incomplete strategy% (5196)------------------------------
% 1.38/0.55  % (5196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5196)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5196)Memory used [KB]: 10618
% 1.38/0.55  % (5196)Time elapsed: 0.137 s
% 1.38/0.55  % (5196)------------------------------
% 1.38/0.55  % (5196)------------------------------
% 1.38/0.55  % (5181)Refutation not found, incomplete strategy% (5181)------------------------------
% 1.38/0.55  % (5181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5181)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5181)Memory used [KB]: 1663
% 1.38/0.55  % (5181)Time elapsed: 0.131 s
% 1.38/0.55  % (5181)------------------------------
% 1.38/0.55  % (5181)------------------------------
% 1.38/0.55  % (5194)Refutation not found, incomplete strategy% (5194)------------------------------
% 1.38/0.55  % (5194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (5194)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (5194)Memory used [KB]: 1918
% 1.38/0.55  % (5194)Time elapsed: 0.086 s
% 1.38/0.55  % (5194)------------------------------
% 1.38/0.55  % (5194)------------------------------
% 1.38/0.56  % (5188)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.56  % (5189)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.56  % (5197)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.57  % (5197)Refutation not found, incomplete strategy% (5197)------------------------------
% 1.38/0.57  % (5197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (5197)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (5197)Memory used [KB]: 1791
% 1.38/0.57  % (5197)Time elapsed: 0.157 s
% 1.38/0.57  % (5197)------------------------------
% 1.38/0.57  % (5197)------------------------------
% 1.96/0.64  % (5218)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.96/0.67  % (5210)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.96/0.68  % (5215)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.96/0.68  % (5211)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.96/0.68  % (5183)Refutation not found, incomplete strategy% (5183)------------------------------
% 1.96/0.68  % (5183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.68  % (5183)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.68  
% 1.96/0.68  % (5183)Memory used [KB]: 6268
% 1.96/0.68  % (5183)Time elapsed: 0.267 s
% 1.96/0.68  % (5183)------------------------------
% 1.96/0.68  % (5183)------------------------------
% 1.96/0.68  % (5212)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.96/0.68  % (5212)Refutation not found, incomplete strategy% (5212)------------------------------
% 1.96/0.68  % (5212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.68  % (5212)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.68  
% 1.96/0.68  % (5212)Memory used [KB]: 6268
% 1.96/0.68  % (5212)Time elapsed: 0.103 s
% 1.96/0.68  % (5212)------------------------------
% 1.96/0.68  % (5212)------------------------------
% 2.27/0.69  % (5213)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.27/0.69  % (5214)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.27/0.69  % (5217)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.27/0.71  % (5213)Refutation found. Thanks to Tanya!
% 2.27/0.71  % SZS status Theorem for theBenchmark
% 2.27/0.72  % (5219)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.27/0.72  % (5214)Refutation not found, incomplete strategy% (5214)------------------------------
% 2.27/0.72  % (5214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.72  % (5214)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.72  
% 2.27/0.72  % (5214)Memory used [KB]: 11001
% 2.27/0.72  % (5214)Time elapsed: 0.123 s
% 2.27/0.72  % (5214)------------------------------
% 2.27/0.72  % (5214)------------------------------
% 2.27/0.73  % SZS output start Proof for theBenchmark
% 2.27/0.73  fof(f1034,plain,(
% 2.27/0.73    $false),
% 2.27/0.73    inference(avatar_sat_refutation,[],[f638,f1033])).
% 2.27/0.73  fof(f1033,plain,(
% 2.27/0.73    ~spl4_1),
% 2.27/0.73    inference(avatar_contradiction_clause,[],[f1032])).
% 2.27/0.73  fof(f1032,plain,(
% 2.27/0.73    $false | ~spl4_1),
% 2.27/0.73    inference(subsumption_resolution,[],[f1031,f181])).
% 2.27/0.73  % (5216)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.27/0.73  fof(f181,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 2.27/0.73    inference(forward_demodulation,[],[f172,f138])).
% 2.27/0.73  fof(f138,plain,(
% 2.27/0.73    ( ! [X0] : (k9_relat_1(sK3,X0) = k2_relat_1(k7_relat_1(sK3,X0))) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f75])).
% 2.27/0.73  fof(f75,plain,(
% 2.27/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f38])).
% 2.27/0.73  fof(f38,plain,(
% 2.27/0.73    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.27/0.73    inference(ennf_transformation,[],[f20])).
% 2.27/0.73  fof(f20,axiom,(
% 2.27/0.73    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.27/0.73  fof(f127,plain,(
% 2.27/0.73    v1_relat_1(sK3)),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f71,f59,f70])).
% 2.27/0.73  fof(f70,plain,(
% 2.27/0.73    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f36])).
% 2.27/0.73  fof(f36,plain,(
% 2.27/0.73    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.27/0.73    inference(ennf_transformation,[],[f17])).
% 2.27/0.73  fof(f17,axiom,(
% 2.27/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.27/0.73  fof(f59,plain,(
% 2.27/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.27/0.73    inference(cnf_transformation,[],[f48])).
% 2.27/0.73  fof(f48,plain,(
% 2.27/0.73    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 2.27/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f47])).
% 2.27/0.73  fof(f47,plain,(
% 2.27/0.73    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 2.27/0.73    introduced(choice_axiom,[])).
% 2.27/0.73  fof(f32,plain,(
% 2.27/0.73    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.27/0.73    inference(flattening,[],[f31])).
% 2.27/0.73  fof(f31,plain,(
% 2.27/0.73    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.27/0.73    inference(ennf_transformation,[],[f30])).
% 2.27/0.73  fof(f30,negated_conjecture,(
% 2.27/0.73    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.27/0.73    inference(negated_conjecture,[],[f29])).
% 2.27/0.73  fof(f29,conjecture,(
% 2.27/0.73    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 2.27/0.73  fof(f71,plain,(
% 2.27/0.73    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.27/0.73    inference(cnf_transformation,[],[f19])).
% 2.27/0.73  fof(f19,axiom,(
% 2.27/0.73    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.27/0.73  fof(f172,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),k2_relat_1(sK3))) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f137,f161,f69])).
% 2.27/0.73  fof(f69,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f35])).
% 2.27/0.73  fof(f35,plain,(
% 2.27/0.73    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.27/0.73    inference(flattening,[],[f34])).
% 2.27/0.73  fof(f34,plain,(
% 2.27/0.73    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.27/0.73    inference(ennf_transformation,[],[f23])).
% 2.27/0.73  fof(f23,axiom,(
% 2.27/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 2.27/0.73  fof(f161,plain,(
% 2.27/0.73    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f145,f70])).
% 2.27/0.73  fof(f145,plain,(
% 2.27/0.73    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f137,f85])).
% 2.27/0.73  fof(f85,plain,(
% 2.27/0.73    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f52])).
% 2.27/0.73  fof(f52,plain,(
% 2.27/0.73    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.27/0.73    inference(nnf_transformation,[],[f16])).
% 2.27/0.73  fof(f16,axiom,(
% 2.27/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.27/0.73  fof(f137,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f74])).
% 2.27/0.73  fof(f74,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f37])).
% 2.27/0.73  fof(f37,plain,(
% 2.27/0.73    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.27/0.73    inference(ennf_transformation,[],[f25])).
% 2.27/0.73  fof(f25,axiom,(
% 2.27/0.73    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.27/0.73  fof(f1031,plain,(
% 2.27/0.73    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_1),
% 2.27/0.73    inference(forward_demodulation,[],[f1023,f123])).
% 2.27/0.73  fof(f123,plain,(
% 2.27/0.73    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f59,f97])).
% 2.27/0.73  fof(f97,plain,(
% 2.27/0.73    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f46])).
% 2.27/0.73  fof(f46,plain,(
% 2.27/0.73    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.73    inference(ennf_transformation,[],[f28])).
% 2.27/0.73  fof(f28,axiom,(
% 2.27/0.73    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 2.27/0.73  fof(f1023,plain,(
% 2.27/0.73    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | ~spl4_1),
% 2.27/0.73    inference(superposition,[],[f61,f692])).
% 2.27/0.73  fof(f692,plain,(
% 2.27/0.73    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f57,f688,f79])).
% 2.27/0.73  fof(f79,plain,(
% 2.27/0.73    ( ! [X0,X1] : (k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f42])).
% 2.27/0.73  fof(f42,plain,(
% 2.27/0.73    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.27/0.73    inference(flattening,[],[f41])).
% 2.27/0.73  fof(f41,plain,(
% 2.27/0.73    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.27/0.73    inference(ennf_transformation,[],[f26])).
% 2.27/0.73  fof(f26,axiom,(
% 2.27/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 2.27/0.73  fof(f688,plain,(
% 2.27/0.73    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f142,f640,f83])).
% 2.27/0.73  fof(f83,plain,(
% 2.27/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.27/0.73    inference(cnf_transformation,[],[f51])).
% 2.27/0.73  fof(f51,plain,(
% 2.27/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.73    inference(flattening,[],[f50])).
% 2.27/0.73  fof(f50,plain,(
% 2.27/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.73    inference(nnf_transformation,[],[f1])).
% 2.27/0.73  fof(f1,axiom,(
% 2.27/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.27/0.73  fof(f640,plain,(
% 2.27/0.73    r1_tarski(k1_tarski(sK0),k1_relat_1(sK3)) | ~spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f254,f87])).
% 2.27/0.73  fof(f87,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f53])).
% 2.27/0.73  fof(f53,plain,(
% 2.27/0.73    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.27/0.73    inference(nnf_transformation,[],[f13])).
% 2.27/0.73  fof(f13,axiom,(
% 2.27/0.73    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.27/0.73  fof(f254,plain,(
% 2.27/0.73    r2_hidden(sK0,k1_relat_1(sK3)) | ~spl4_1),
% 2.27/0.73    inference(avatar_component_clause,[],[f253])).
% 2.27/0.73  fof(f253,plain,(
% 2.27/0.73    spl4_1 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 2.27/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.27/0.73  fof(f142,plain,(
% 2.27/0.73    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f124,f76])).
% 2.27/0.73  fof(f76,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f49])).
% 2.27/0.73  fof(f49,plain,(
% 2.27/0.73    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.27/0.73    inference(nnf_transformation,[],[f39])).
% 2.27/0.73  fof(f39,plain,(
% 2.27/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.27/0.73    inference(ennf_transformation,[],[f18])).
% 2.27/0.73  fof(f18,axiom,(
% 2.27/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.27/0.73  fof(f124,plain,(
% 2.27/0.73    v4_relat_1(sK3,k1_tarski(sK0))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f59,f94])).
% 2.27/0.73  fof(f94,plain,(
% 2.27/0.73    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.27/0.73    inference(cnf_transformation,[],[f45])).
% 2.27/0.73  fof(f45,plain,(
% 2.27/0.73    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.27/0.73    inference(ennf_transformation,[],[f27])).
% 2.27/0.73  fof(f27,axiom,(
% 2.27/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.27/0.73  fof(f57,plain,(
% 2.27/0.73    v1_funct_1(sK3)),
% 2.27/0.73    inference(cnf_transformation,[],[f48])).
% 2.27/0.73  fof(f61,plain,(
% 2.27/0.73    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.27/0.73    inference(cnf_transformation,[],[f48])).
% 2.27/0.73  fof(f638,plain,(
% 2.27/0.73    spl4_1),
% 2.27/0.73    inference(avatar_contradiction_clause,[],[f637])).
% 2.27/0.73  fof(f637,plain,(
% 2.27/0.73    $false | spl4_1),
% 2.27/0.73    inference(subsumption_resolution,[],[f636,f64])).
% 2.27/0.73  fof(f64,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f4])).
% 2.27/0.73  fof(f4,axiom,(
% 2.27/0.73    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.27/0.73  fof(f636,plain,(
% 2.27/0.73    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_1),
% 2.27/0.73    inference(superposition,[],[f327,f479])).
% 2.27/0.73  fof(f479,plain,(
% 2.27/0.73    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f64,f345,f83])).
% 2.27/0.73  fof(f345,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | spl4_1),
% 2.27/0.73    inference(forward_demodulation,[],[f324,f63])).
% 2.27/0.73  fof(f63,plain,(
% 2.27/0.73    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.27/0.73    inference(cnf_transformation,[],[f24])).
% 2.27/0.73  fof(f24,axiom,(
% 2.27/0.73    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.27/0.73  fof(f324,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(k9_relat_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))) ) | spl4_1),
% 2.27/0.73    inference(superposition,[],[f181,f295])).
% 2.27/0.73  fof(f295,plain,(
% 2.27/0.73    k1_xboole_0 = sK3 | spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f64,f281,f83])).
% 2.27/0.73  fof(f281,plain,(
% 2.27/0.73    r1_tarski(sK3,k1_xboole_0) | spl4_1),
% 2.27/0.73    inference(forward_demodulation,[],[f264,f104])).
% 2.27/0.73  fof(f104,plain,(
% 2.27/0.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.27/0.73    inference(equality_resolution,[],[f89])).
% 2.27/0.73  fof(f89,plain,(
% 2.27/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.27/0.73    inference(cnf_transformation,[],[f55])).
% 2.27/0.73  fof(f55,plain,(
% 2.27/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.27/0.73    inference(flattening,[],[f54])).
% 2.27/0.73  fof(f54,plain,(
% 2.27/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.27/0.73    inference(nnf_transformation,[],[f14])).
% 2.27/0.73  fof(f14,axiom,(
% 2.27/0.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.27/0.73  fof(f264,plain,(
% 2.27/0.73    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | spl4_1),
% 2.27/0.73    inference(superposition,[],[f128,f263])).
% 2.27/0.73  fof(f263,plain,(
% 2.27/0.73    k1_xboole_0 = k1_relat_1(sK3) | spl4_1),
% 2.27/0.73    inference(forward_demodulation,[],[f261,f250])).
% 2.27/0.73  fof(f250,plain,(
% 2.27/0.73    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.27/0.73    inference(forward_demodulation,[],[f249,f65])).
% 2.27/0.73  fof(f65,plain,(
% 2.27/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f5])).
% 2.27/0.73  fof(f5,axiom,(
% 2.27/0.73    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.27/0.73  fof(f249,plain,(
% 2.27/0.73    k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0)) = k5_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3))),
% 2.27/0.73    inference(superposition,[],[f73,f149])).
% 2.27/0.73  fof(f149,plain,(
% 2.27/0.73    k1_relat_1(sK3) = k3_xboole_0(k1_relat_1(sK3),k1_tarski(sK0))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f142,f78])).
% 2.27/0.73  fof(f78,plain,(
% 2.27/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.27/0.73    inference(cnf_transformation,[],[f40])).
% 2.27/0.73  fof(f40,plain,(
% 2.27/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.27/0.73    inference(ennf_transformation,[],[f3])).
% 2.27/0.73  fof(f3,axiom,(
% 2.27/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.27/0.73  fof(f73,plain,(
% 2.27/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.27/0.73    inference(cnf_transformation,[],[f2])).
% 2.27/0.73  fof(f2,axiom,(
% 2.27/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.27/0.73  fof(f261,plain,(
% 2.27/0.73    k1_relat_1(sK3) = k4_xboole_0(k1_relat_1(sK3),k1_tarski(sK0)) | spl4_1),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f255,f92])).
% 2.27/0.73  fof(f92,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 2.27/0.73    inference(cnf_transformation,[],[f56])).
% 2.27/0.73  fof(f56,plain,(
% 2.27/0.73    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.27/0.73    inference(nnf_transformation,[],[f15])).
% 2.27/0.73  fof(f15,axiom,(
% 2.27/0.73    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.27/0.73  fof(f255,plain,(
% 2.27/0.73    ~r2_hidden(sK0,k1_relat_1(sK3)) | spl4_1),
% 2.27/0.73    inference(avatar_component_clause,[],[f253])).
% 2.27/0.73  fof(f128,plain,(
% 2.27/0.73    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f127,f67])).
% 2.27/0.73  fof(f67,plain,(
% 2.27/0.73    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.27/0.73    inference(cnf_transformation,[],[f33])).
% 2.27/0.73  fof(f33,plain,(
% 2.27/0.73    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.27/0.73    inference(ennf_transformation,[],[f22])).
% 2.27/0.73  fof(f22,axiom,(
% 2.27/0.73    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.27/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 2.27/0.73  fof(f327,plain,(
% 2.27/0.73    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_1),
% 2.27/0.73    inference(superposition,[],[f225,f295])).
% 2.27/0.73  fof(f225,plain,(
% 2.27/0.73    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f155,f85])).
% 2.27/0.73  fof(f155,plain,(
% 2.27/0.73    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))),
% 2.27/0.73    inference(forward_demodulation,[],[f154,f123])).
% 2.27/0.73  fof(f154,plain,(
% 2.27/0.73    ~m1_subset_1(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_zfmisc_1(k1_tarski(k1_funct_1(sK3,sK0))))),
% 2.27/0.73    inference(unit_resulting_resolution,[],[f61,f84])).
% 2.27/0.73  fof(f84,plain,(
% 2.27/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.27/0.73    inference(cnf_transformation,[],[f52])).
% 2.27/0.73  % SZS output end Proof for theBenchmark
% 2.27/0.73  % (5213)------------------------------
% 2.27/0.73  % (5213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.73  % (5213)Termination reason: Refutation
% 2.27/0.73  
% 2.27/0.73  % (5213)Memory used [KB]: 11129
% 2.27/0.73  % (5213)Time elapsed: 0.122 s
% 2.27/0.73  % (5213)------------------------------
% 2.27/0.73  % (5213)------------------------------
% 2.27/0.73  % (5179)Success in time 0.367 s
%------------------------------------------------------------------------------

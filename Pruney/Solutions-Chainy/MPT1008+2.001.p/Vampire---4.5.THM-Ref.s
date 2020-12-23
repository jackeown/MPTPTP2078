%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 785 expanded)
%              Number of leaves         :   17 ( 186 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 (3029 expanded)
%              Number of equality atoms :   94 (1117 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(subsumption_resolution,[],[f436,f185])).

fof(f185,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f132,f170])).

fof(f170,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(superposition,[],[f132,f119])).

% (17543)Refutation not found, incomplete strategy% (17543)------------------------------
% (17543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17543)Termination reason: Refutation not found, incomplete strategy

% (17543)Memory used [KB]: 10618
% (17543)Time elapsed: 0.111 s
% (17543)------------------------------
% (17543)------------------------------
fof(f119,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f117,plain,(
    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f114,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

% (17550)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f114,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f98,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f132,plain,(
    k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f131,f100])).

fof(f131,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f130,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f104,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f104,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f58,f99])).

fof(f99,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f56,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f436,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f206,f315])).

fof(f315,plain,(
    ! [X0] : r1_tarski(k1_tarski(sK0),X0) ),
    inference(resolution,[],[f258,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f258,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f257,f202])).

fof(f202,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f187,f199])).

fof(f199,plain,(
    ! [X2] : v4_relat_1(sK2,X2) ),
    inference(subsumption_resolution,[],[f175,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f175,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | v4_relat_1(sK2,X2) ) ),
    inference(backward_demodulation,[],[f109,f170])).

fof(f109,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK2),X2)
      | v4_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f187,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(backward_demodulation,[],[f135,f170])).

fof(f135,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK2))
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f108,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(sK2),X1)
      | ~ v4_relat_1(sK2,X1) ) ),
    inference(resolution,[],[f100,f70])).

fof(f257,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f242,f61])).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f242,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f103,f231])).

fof(f231,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f105,f170])).

fof(f105,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(backward_demodulation,[],[f96,f99])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(subsumption_resolution,[],[f95,f54])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f94,f56])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f55,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f55,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f205,f170])).

fof(f205,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f173,f204])).

fof(f204,plain,(
    ! [X2] : sK2 = k7_relat_1(sK2,X2) ),
    inference(subsumption_resolution,[],[f193,f62])).

fof(f193,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | sK2 = k7_relat_1(sK2,X2) ) ),
    inference(backward_demodulation,[],[f150,f170])).

fof(f150,plain,(
    ! [X2] :
      ( sK2 = k7_relat_1(sK2,X2)
      | ~ r1_tarski(k1_relat_1(sK2),X2) ) ),
    inference(subsumption_resolution,[],[f149,f100])).

fof(f149,plain,(
    ! [X2] :
      ( sK2 = k7_relat_1(sK2,X2)
      | ~ r1_tarski(k1_relat_1(sK2),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f111,f71])).

fof(f111,plain,(
    ! [X4] :
      ( ~ v4_relat_1(sK2,X4)
      | sK2 = k7_relat_1(sK2,X4) ) ),
    inference(resolution,[],[f100,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f173,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f107,f170])).

fof(f107,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (17533)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.48  % (17556)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (17557)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.49  % (17538)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.49  % (17540)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (17536)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (17537)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (17549)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.50  % (17537)Refutation not found, incomplete strategy% (17537)------------------------------
% 0.19/0.50  % (17537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (17537)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (17537)Memory used [KB]: 6268
% 0.19/0.50  % (17537)Time elapsed: 0.099 s
% 0.19/0.50  % (17537)------------------------------
% 0.19/0.50  % (17537)------------------------------
% 0.19/0.50  % (17547)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (17543)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (17556)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f443,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f436,f185])).
% 0.19/0.50  fof(f185,plain,(
% 0.19/0.50    k1_xboole_0 != k1_tarski(sK0)),
% 0.19/0.50    inference(backward_demodulation,[],[f132,f170])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f162])).
% 0.19/0.50  fof(f162,plain,(
% 0.19/0.50    k1_tarski(sK0) != k1_tarski(sK0) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.50    inference(superposition,[],[f132,f119])).
% 0.19/0.50  % (17543)Refutation not found, incomplete strategy% (17543)------------------------------
% 0.19/0.50  % (17543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (17543)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (17543)Memory used [KB]: 10618
% 0.19/0.50  % (17543)Time elapsed: 0.111 s
% 0.19/0.50  % (17543)------------------------------
% 0.19/0.50  % (17543)------------------------------
% 0.19/0.50  fof(f119,plain,(
% 0.19/0.50    k1_tarski(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.50    inference(resolution,[],[f117,f77])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.19/0.50    inference(flattening,[],[f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.19/0.50  fof(f117,plain,(
% 0.19/0.50    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f114,f100])).
% 0.19/0.50  fof(f100,plain,(
% 0.19/0.50    v1_relat_1(sK2)),
% 0.19/0.50    inference(resolution,[],[f56,f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.19/0.50    inference(cnf_transformation,[],[f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f23])).
% 0.19/0.50  % (17550)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.50  fof(f23,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.19/0.50    inference(negated_conjecture,[],[f22])).
% 0.19/0.50  fof(f22,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    r1_tarski(k1_relat_1(sK2),k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 0.19/0.50    inference(resolution,[],[f98,f70])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(nnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    v4_relat_1(sK2,k1_tarski(sK0))),
% 0.19/0.50    inference(resolution,[],[f56,f84])).
% 0.19/0.51  fof(f84,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.51  fof(f132,plain,(
% 0.19/0.51    k1_tarski(sK0) != k1_relat_1(sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f131,f100])).
% 0.19/0.51  fof(f131,plain,(
% 0.19/0.51    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f130,f54])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    v1_funct_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f46])).
% 0.19/0.51  fof(f130,plain,(
% 0.19/0.51    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f128])).
% 0.19/0.51  fof(f128,plain,(
% 0.19/0.51    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(superposition,[],[f104,f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,axiom,(
% 0.19/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.19/0.51    inference(backward_demodulation,[],[f58,f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.19/0.51    inference(resolution,[],[f56,f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f39])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f46])).
% 0.19/0.51  fof(f436,plain,(
% 0.19/0.51    k1_xboole_0 = k1_tarski(sK0)),
% 0.19/0.51    inference(resolution,[],[f206,f315])).
% 0.19/0.51  fof(f315,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(k1_tarski(sK0),X0)) )),
% 0.19/0.51    inference(resolution,[],[f258,f75])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(rectify,[],[f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(nnf_transformation,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.51  fof(f258,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f257,f202])).
% 0.19/0.51  fof(f202,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f187,f199])).
% 0.19/0.51  fof(f199,plain,(
% 0.19/0.51    ( ! [X2] : (v4_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f175,f62])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.51  fof(f175,plain,(
% 0.19/0.51    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | v4_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f109,f170])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | v4_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(resolution,[],[f100,f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f47])).
% 0.19/0.51  fof(f187,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~v4_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f135,f170])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK2)) | ~v4_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(resolution,[],[f108,f80])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,axiom,(
% 0.19/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(k1_relat_1(sK2),X1) | ~v4_relat_1(sK2,X1)) )),
% 0.19/0.51    inference(resolution,[],[f100,f70])).
% 0.19/0.51  fof(f257,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.19/0.51    inference(forward_demodulation,[],[f242,f61])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.51  fof(f242,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k2_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.19/0.51    inference(backward_demodulation,[],[f103,f231])).
% 0.19/0.51  fof(f231,plain,(
% 0.19/0.51    k1_xboole_0 = sK2),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f224])).
% 0.19/0.51  fof(f224,plain,(
% 0.19/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.19/0.51    inference(superposition,[],[f105,f170])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.19/0.51    inference(resolution,[],[f100,f66])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.19/0.51    inference(backward_demodulation,[],[f96,f99])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f95,f54])).
% 0.19/0.51  fof(f95,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~v1_funct_1(sK2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f94,f56])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f92,f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    k1_xboole_0 != sK1),
% 0.19/0.51    inference(cnf_transformation,[],[f46])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(k1_tarski(sK0),sK1,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_1(sK2)) )),
% 0.19/0.51    inference(resolution,[],[f55,f87])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f44])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.51    inference(flattening,[],[f43])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.51    inference(ennf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,axiom,(
% 0.19/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f46])).
% 0.19/0.51  fof(f206,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(forward_demodulation,[],[f205,f170])).
% 0.19/0.51  fof(f205,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(sK2) = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f173,f204])).
% 0.19/0.51  fof(f204,plain,(
% 0.19/0.51    ( ! [X2] : (sK2 = k7_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f193,f62])).
% 0.19/0.51  fof(f193,plain,(
% 0.19/0.51    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | sK2 = k7_relat_1(sK2,X2)) )),
% 0.19/0.51    inference(backward_demodulation,[],[f150,f170])).
% 0.19/0.51  fof(f150,plain,(
% 0.19/0.51    ( ! [X2] : (sK2 = k7_relat_1(sK2,X2) | ~r1_tarski(k1_relat_1(sK2),X2)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f149,f100])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    ( ! [X2] : (sK2 = k7_relat_1(sK2,X2) | ~r1_tarski(k1_relat_1(sK2),X2) | ~v1_relat_1(sK2)) )),
% 0.19/0.51    inference(resolution,[],[f111,f71])).
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    ( ! [X4] : (~v4_relat_1(sK2,X4) | sK2 = k7_relat_1(sK2,X4)) )),
% 0.19/0.51    inference(resolution,[],[f100,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.51  fof(f173,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_relat_1(k7_relat_1(sK2,X0)) = X0) )),
% 0.19/0.51    inference(backward_demodulation,[],[f107,f170])).
% 0.19/0.51  fof(f107,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(sK2))) )),
% 0.19/0.51    inference(resolution,[],[f100,f69])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (17556)------------------------------
% 0.19/0.51  % (17556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (17556)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (17556)Memory used [KB]: 1918
% 0.19/0.51  % (17556)Time elapsed: 0.052 s
% 0.19/0.51  % (17556)------------------------------
% 0.19/0.51  % (17556)------------------------------
% 0.19/0.51  % (17532)Success in time 0.164 s
%------------------------------------------------------------------------------

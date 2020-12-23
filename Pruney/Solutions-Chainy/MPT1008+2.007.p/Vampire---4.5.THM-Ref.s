%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:08 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  111 (1137 expanded)
%              Number of leaves         :   18 ( 272 expanded)
%              Depth                    :   27
%              Number of atoms          :  321 (4897 expanded)
%              Number of equality atoms :  120 (2103 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f553,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f553,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f60,f485])).

fof(f485,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f482,f260])).

fof(f260,plain,(
    ! [X1] : v4_relat_1(sK2,X1) ),
    inference(resolution,[],[f252,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f87,f98])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f252,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f246,f98])).

fof(f246,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f197,f244])).

fof(f244,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f243,f229])).

fof(f229,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f184,f227])).

fof(f227,plain,(
    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f225,f111])).

fof(f111,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f44])).

fof(f44,plain,
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

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f225,plain,
    ( k2_relat_1(sK2) = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f202,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f202,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f195,f111])).

fof(f195,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f63,f183])).

fof(f183,plain,(
    k1_tarski(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f181,f56])).

fof(f181,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f179,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f179,plain,(
    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f178,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f45])).

% (16101)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f173,plain,
    ( ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(resolution,[],[f89,f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f41])).

% (16084)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (16088)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f63,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f184,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k2_relat_1(sK2) != k11_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f171,f183])).

fof(f171,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f170,f111])).

fof(f170,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f167,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f167,plain,
    ( k2_relat_1(sK2) != k11_relat_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f147,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f147,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f146,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f58,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f58,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f243,plain,
    ( r2_hidden(sK0,k1_tarski(sK0))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f242,f183])).

fof(f242,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f239,f111])).

fof(f239,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f227,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f197,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f196,f111])).

fof(f196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f54])).

fof(f190,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f67,f183])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f482,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ v4_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f290,f201])).

fof(f201,plain,(
    ! [X1] :
      ( r1_tarski(k1_tarski(sK0),X1)
      | ~ v4_relat_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f194,f111])).

fof(f194,plain,(
    ! [X1] :
      ( r1_tarski(k1_tarski(sK0),X1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f72,f183])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f290,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f289,f111])).

fof(f289,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f278,f258])).

fof(f258,plain,(
    ! [X0] : v5_relat_1(sK2,X0) ),
    inference(resolution,[],[f252,f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X3,X2) ) ),
    inference(superposition,[],[f88,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f278,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ v5_relat_1(sK2,X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f123,f244])).

fof(f123,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f79,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

% (16099)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (805502976)
% 0.14/0.37  ipcrm: permission denied for id (805863425)
% 0.14/0.38  ipcrm: permission denied for id (805994501)
% 0.14/0.38  ipcrm: permission denied for id (806027270)
% 0.14/0.38  ipcrm: permission denied for id (806125576)
% 0.14/0.38  ipcrm: permission denied for id (805535755)
% 0.14/0.39  ipcrm: permission denied for id (806223884)
% 0.14/0.39  ipcrm: permission denied for id (806256653)
% 0.14/0.39  ipcrm: permission denied for id (806289422)
% 0.14/0.39  ipcrm: permission denied for id (806354960)
% 0.14/0.39  ipcrm: permission denied for id (806420498)
% 0.22/0.40  ipcrm: permission denied for id (806551574)
% 0.22/0.40  ipcrm: permission denied for id (806584343)
% 0.22/0.40  ipcrm: permission denied for id (806617112)
% 0.22/0.40  ipcrm: permission denied for id (806682650)
% 0.22/0.41  ipcrm: permission denied for id (806715419)
% 0.22/0.41  ipcrm: permission denied for id (806748188)
% 0.22/0.41  ipcrm: permission denied for id (805634077)
% 0.22/0.41  ipcrm: permission denied for id (806780958)
% 0.22/0.41  ipcrm: permission denied for id (806813727)
% 0.22/0.41  ipcrm: permission denied for id (806846496)
% 0.22/0.41  ipcrm: permission denied for id (806879265)
% 0.22/0.42  ipcrm: permission denied for id (807043110)
% 0.22/0.42  ipcrm: permission denied for id (807075879)
% 0.22/0.42  ipcrm: permission denied for id (807141416)
% 0.22/0.43  ipcrm: permission denied for id (807206954)
% 0.22/0.43  ipcrm: permission denied for id (807272492)
% 0.22/0.43  ipcrm: permission denied for id (807305261)
% 0.22/0.43  ipcrm: permission denied for id (807370799)
% 0.22/0.44  ipcrm: permission denied for id (807469106)
% 0.22/0.44  ipcrm: permission denied for id (807567413)
% 0.22/0.44  ipcrm: permission denied for id (807665720)
% 0.22/0.45  ipcrm: permission denied for id (807731258)
% 0.22/0.45  ipcrm: permission denied for id (807764027)
% 0.22/0.45  ipcrm: permission denied for id (807796796)
% 0.22/0.45  ipcrm: permission denied for id (807829565)
% 0.22/0.45  ipcrm: permission denied for id (807895103)
% 0.22/0.45  ipcrm: permission denied for id (807927872)
% 0.22/0.46  ipcrm: permission denied for id (807960641)
% 0.22/0.46  ipcrm: permission denied for id (807993410)
% 0.22/0.46  ipcrm: permission denied for id (808058948)
% 0.22/0.46  ipcrm: permission denied for id (808157254)
% 0.22/0.46  ipcrm: permission denied for id (808190023)
% 0.22/0.47  ipcrm: permission denied for id (808321099)
% 0.22/0.47  ipcrm: permission denied for id (808452175)
% 0.22/0.48  ipcrm: permission denied for id (808550482)
% 0.22/0.48  ipcrm: permission denied for id (808583251)
% 0.22/0.48  ipcrm: permission denied for id (808681558)
% 0.22/0.48  ipcrm: permission denied for id (805732439)
% 0.22/0.49  ipcrm: permission denied for id (808747097)
% 0.22/0.49  ipcrm: permission denied for id (808812635)
% 0.22/0.49  ipcrm: permission denied for id (805765212)
% 0.22/0.49  ipcrm: permission denied for id (808845405)
% 0.22/0.49  ipcrm: permission denied for id (808878174)
% 0.22/0.49  ipcrm: permission denied for id (808910943)
% 0.22/0.50  ipcrm: permission denied for id (809074788)
% 0.22/0.50  ipcrm: permission denied for id (809107557)
% 0.22/0.50  ipcrm: permission denied for id (805797990)
% 0.22/0.50  ipcrm: permission denied for id (809140327)
% 0.22/0.51  ipcrm: permission denied for id (809238634)
% 0.22/0.51  ipcrm: permission denied for id (809271403)
% 0.22/0.51  ipcrm: permission denied for id (809304172)
% 0.22/0.52  ipcrm: permission denied for id (809500785)
% 0.22/0.52  ipcrm: permission denied for id (809566323)
% 0.22/0.52  ipcrm: permission denied for id (809697399)
% 0.22/0.53  ipcrm: permission denied for id (809730168)
% 0.22/0.53  ipcrm: permission denied for id (809795706)
% 0.22/0.53  ipcrm: permission denied for id (809828475)
% 0.22/0.53  ipcrm: permission denied for id (809861244)
% 0.87/0.63  % (16079)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.87/0.65  % (16087)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.12/0.67  % (16085)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.12/0.67  % (16097)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.12/0.68  % (16078)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.12/0.68  % (16077)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.12/0.69  % (16087)Refutation not found, incomplete strategy% (16087)------------------------------
% 1.12/0.69  % (16087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.69  % (16087)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.69  
% 1.12/0.69  % (16087)Memory used [KB]: 10874
% 1.12/0.69  % (16087)Time elapsed: 0.104 s
% 1.12/0.69  % (16087)------------------------------
% 1.12/0.69  % (16087)------------------------------
% 1.12/0.69  % (16081)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.12/0.70  % (16103)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.12/0.70  % (16093)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.12/0.70  % (16080)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.12/0.70  % (16093)Refutation not found, incomplete strategy% (16093)------------------------------
% 1.12/0.70  % (16093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.70  % (16093)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.70  
% 1.12/0.70  % (16093)Memory used [KB]: 10618
% 1.12/0.70  % (16093)Time elapsed: 0.112 s
% 1.12/0.70  % (16093)------------------------------
% 1.12/0.70  % (16093)------------------------------
% 1.12/0.70  % (16078)Refutation not found, incomplete strategy% (16078)------------------------------
% 1.12/0.70  % (16078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.71  % (16096)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.12/0.71  % (16078)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.71  
% 1.12/0.71  % (16078)Memory used [KB]: 1663
% 1.12/0.71  % (16078)Time elapsed: 0.114 s
% 1.12/0.71  % (16078)------------------------------
% 1.12/0.71  % (16078)------------------------------
% 1.12/0.71  % (16103)Refutation not found, incomplete strategy% (16103)------------------------------
% 1.12/0.71  % (16103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.71  % (16103)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.71  
% 1.12/0.71  % (16103)Memory used [KB]: 6396
% 1.12/0.71  % (16103)Time elapsed: 0.127 s
% 1.12/0.71  % (16103)------------------------------
% 1.12/0.71  % (16103)------------------------------
% 1.12/0.71  % (16094)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.12/0.71  % (16091)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.12/0.71  % (16082)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.12/0.71  % (16086)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.12/0.71  % (16083)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.12/0.71  % (16100)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.12/0.72  % (16092)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.12/0.72  % (16086)Refutation found. Thanks to Tanya!
% 1.12/0.72  % SZS status Theorem for theBenchmark
% 1.12/0.72  % (16104)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.12/0.72  % (16106)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.12/0.72  % (16106)Refutation not found, incomplete strategy% (16106)------------------------------
% 1.12/0.72  % (16106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.72  % (16106)Termination reason: Refutation not found, incomplete strategy
% 1.12/0.72  
% 1.12/0.72  % (16106)Memory used [KB]: 1663
% 1.12/0.72  % (16106)Time elapsed: 0.135 s
% 1.12/0.72  % (16106)------------------------------
% 1.12/0.72  % (16106)------------------------------
% 1.12/0.72  % (16098)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.12/0.72  % (16089)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.12/0.72  % (16102)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.65/0.73  % SZS output start Proof for theBenchmark
% 1.65/0.73  fof(f554,plain,(
% 1.65/0.73    $false),
% 1.65/0.73    inference(subsumption_resolution,[],[f553,f59])).
% 1.65/0.73  fof(f59,plain,(
% 1.65/0.73    v1_xboole_0(k1_xboole_0)),
% 1.65/0.73    inference(cnf_transformation,[],[f1])).
% 1.65/0.73  fof(f1,axiom,(
% 1.65/0.73    v1_xboole_0(k1_xboole_0)),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.65/0.73  fof(f553,plain,(
% 1.65/0.73    ~v1_xboole_0(k1_xboole_0)),
% 1.65/0.73    inference(superposition,[],[f60,f485])).
% 1.65/0.73  fof(f485,plain,(
% 1.65/0.73    k1_xboole_0 = k1_tarski(sK0)),
% 1.65/0.73    inference(subsumption_resolution,[],[f482,f260])).
% 1.65/0.73  fof(f260,plain,(
% 1.65/0.73    ( ! [X1] : (v4_relat_1(sK2,X1)) )),
% 1.65/0.73    inference(resolution,[],[f252,f127])).
% 1.65/0.73  fof(f127,plain,(
% 1.65/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.65/0.73    inference(superposition,[],[f87,f98])).
% 1.65/0.73  fof(f98,plain,(
% 1.65/0.73    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.65/0.73    inference(equality_resolution,[],[f82])).
% 1.65/0.73  fof(f82,plain,(
% 1.65/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.65/0.73    inference(cnf_transformation,[],[f52])).
% 1.65/0.73  fof(f52,plain,(
% 1.65/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/0.73    inference(flattening,[],[f51])).
% 1.65/0.73  fof(f51,plain,(
% 1.65/0.73    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.65/0.73    inference(nnf_transformation,[],[f7])).
% 1.65/0.73  fof(f7,axiom,(
% 1.65/0.73    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.65/0.73  fof(f87,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f39])).
% 1.65/0.73  fof(f39,plain,(
% 1.65/0.73    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(ennf_transformation,[],[f18])).
% 1.65/0.73  fof(f18,axiom,(
% 1.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.65/0.73  fof(f252,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.65/0.73    inference(forward_demodulation,[],[f246,f98])).
% 1.65/0.73  fof(f246,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k1_xboole_0)))),
% 1.65/0.73    inference(backward_demodulation,[],[f197,f244])).
% 1.65/0.73  fof(f244,plain,(
% 1.65/0.73    k1_xboole_0 = k2_relat_1(sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f243,f229])).
% 1.65/0.73  fof(f229,plain,(
% 1.65/0.73    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.65/0.73    inference(trivial_inequality_removal,[],[f228])).
% 1.65/0.73  fof(f228,plain,(
% 1.65/0.73    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.65/0.73    inference(backward_demodulation,[],[f184,f227])).
% 1.65/0.73  fof(f227,plain,(
% 1.65/0.73    k2_relat_1(sK2) = k11_relat_1(sK2,sK0)),
% 1.65/0.73    inference(subsumption_resolution,[],[f225,f111])).
% 1.65/0.73  fof(f111,plain,(
% 1.65/0.73    v1_relat_1(sK2)),
% 1.65/0.73    inference(resolution,[],[f84,f56])).
% 1.65/0.73  fof(f56,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.65/0.73    inference(cnf_transformation,[],[f45])).
% 1.65/0.73  fof(f45,plain,(
% 1.65/0.73    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.65/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f44])).
% 1.65/0.73  fof(f44,plain,(
% 1.65/0.73    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.65/0.73    introduced(choice_axiom,[])).
% 1.65/0.73  fof(f26,plain,(
% 1.65/0.73    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.65/0.73    inference(flattening,[],[f25])).
% 1.65/0.73  fof(f25,plain,(
% 1.65/0.73    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.65/0.73    inference(ennf_transformation,[],[f24])).
% 1.65/0.73  fof(f24,negated_conjecture,(
% 1.65/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.65/0.73    inference(negated_conjecture,[],[f23])).
% 1.65/0.73  fof(f23,conjecture,(
% 1.65/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.65/0.73  fof(f84,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f36])).
% 1.65/0.73  fof(f36,plain,(
% 1.65/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(ennf_transformation,[],[f17])).
% 1.65/0.73  fof(f17,axiom,(
% 1.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.73  fof(f225,plain,(
% 1.65/0.73    k2_relat_1(sK2) = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(superposition,[],[f202,f64])).
% 1.65/0.73  fof(f64,plain,(
% 1.65/0.73    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f28])).
% 1.65/0.73  fof(f28,plain,(
% 1.65/0.73    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.65/0.73    inference(ennf_transformation,[],[f10])).
% 1.65/0.73  fof(f10,axiom,(
% 1.65/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.65/0.73  fof(f202,plain,(
% 1.65/0.73    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))),
% 1.65/0.73    inference(subsumption_resolution,[],[f195,f111])).
% 1.65/0.73  fof(f195,plain,(
% 1.65/0.73    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(superposition,[],[f63,f183])).
% 1.65/0.73  fof(f183,plain,(
% 1.65/0.73    k1_tarski(sK0) = k1_relat_1(sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f181,f56])).
% 1.65/0.73  fof(f181,plain,(
% 1.65/0.73    k1_tarski(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.65/0.73    inference(superposition,[],[f179,f86])).
% 1.65/0.73  fof(f86,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.73    inference(cnf_transformation,[],[f38])).
% 1.65/0.73  fof(f38,plain,(
% 1.65/0.73    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(ennf_transformation,[],[f19])).
% 1.65/0.73  fof(f19,axiom,(
% 1.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.73  fof(f179,plain,(
% 1.65/0.73    k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f178,f57])).
% 1.65/0.73  fof(f57,plain,(
% 1.65/0.73    k1_xboole_0 != sK1),
% 1.65/0.73    inference(cnf_transformation,[],[f45])).
% 1.65/0.73  fof(f178,plain,(
% 1.65/0.73    k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f173,f55])).
% 1.65/0.73  fof(f55,plain,(
% 1.65/0.73    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.65/0.73    inference(cnf_transformation,[],[f45])).
% 1.65/0.73  % (16101)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.65/0.73  fof(f173,plain,(
% 1.65/0.73    ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | k1_xboole_0 = sK1 | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)),
% 1.65/0.73    inference(resolution,[],[f89,f56])).
% 1.65/0.73  fof(f89,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.65/0.73    inference(cnf_transformation,[],[f53])).
% 1.65/0.73  fof(f53,plain,(
% 1.65/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(nnf_transformation,[],[f41])).
% 1.65/0.73  % (16084)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.65/0.73  % (16088)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.65/0.73  fof(f41,plain,(
% 1.65/0.73    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(flattening,[],[f40])).
% 1.65/0.73  fof(f40,plain,(
% 1.65/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(ennf_transformation,[],[f21])).
% 1.65/0.73  fof(f21,axiom,(
% 1.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.65/0.73  fof(f63,plain,(
% 1.65/0.73    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f27])).
% 1.65/0.73  fof(f27,plain,(
% 1.65/0.73    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.73    inference(ennf_transformation,[],[f14])).
% 1.65/0.73  fof(f14,axiom,(
% 1.65/0.73    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.65/0.73  fof(f184,plain,(
% 1.65/0.73    ~r2_hidden(sK0,k1_tarski(sK0)) | k2_relat_1(sK2) != k11_relat_1(sK2,sK0)),
% 1.65/0.73    inference(backward_demodulation,[],[f171,f183])).
% 1.65/0.73  fof(f171,plain,(
% 1.65/0.73    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.65/0.73    inference(subsumption_resolution,[],[f170,f111])).
% 1.65/0.73  fof(f170,plain,(
% 1.65/0.73    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f167,f54])).
% 1.65/0.73  fof(f54,plain,(
% 1.65/0.73    v1_funct_1(sK2)),
% 1.65/0.73    inference(cnf_transformation,[],[f45])).
% 1.65/0.73  fof(f167,plain,(
% 1.65/0.73    k2_relat_1(sK2) != k11_relat_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(superposition,[],[f147,f76])).
% 1.65/0.73  fof(f76,plain,(
% 1.65/0.73    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f35])).
% 1.65/0.73  fof(f35,plain,(
% 1.65/0.73    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(flattening,[],[f34])).
% 1.65/0.73  fof(f34,plain,(
% 1.65/0.73    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.65/0.73    inference(ennf_transformation,[],[f16])).
% 1.65/0.73  fof(f16,axiom,(
% 1.65/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.65/0.73  fof(f147,plain,(
% 1.65/0.73    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f146,f56])).
% 1.65/0.73  fof(f146,plain,(
% 1.65/0.73    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.65/0.73    inference(superposition,[],[f58,f85])).
% 1.65/0.73  fof(f85,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.73    inference(cnf_transformation,[],[f37])).
% 1.65/0.73  fof(f37,plain,(
% 1.65/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.73    inference(ennf_transformation,[],[f20])).
% 1.65/0.73  fof(f20,axiom,(
% 1.65/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.65/0.73  fof(f58,plain,(
% 1.65/0.73    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.65/0.73    inference(cnf_transformation,[],[f45])).
% 1.65/0.73  fof(f243,plain,(
% 1.65/0.73    r2_hidden(sK0,k1_tarski(sK0)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.65/0.73    inference(forward_demodulation,[],[f242,f183])).
% 1.65/0.73  fof(f242,plain,(
% 1.65/0.73    k1_xboole_0 = k2_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2))),
% 1.65/0.73    inference(subsumption_resolution,[],[f239,f111])).
% 1.65/0.73  fof(f239,plain,(
% 1.65/0.73    k1_xboole_0 = k2_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(superposition,[],[f227,f75])).
% 1.65/0.73  fof(f75,plain,(
% 1.65/0.73    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f48])).
% 1.65/0.73  fof(f48,plain,(
% 1.65/0.73    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(nnf_transformation,[],[f33])).
% 1.65/0.73  fof(f33,plain,(
% 1.65/0.73    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(ennf_transformation,[],[f15])).
% 1.65/0.73  fof(f15,axiom,(
% 1.65/0.73    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.65/0.73  fof(f197,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2))))),
% 1.65/0.73    inference(subsumption_resolution,[],[f196,f111])).
% 1.65/0.73  fof(f196,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(subsumption_resolution,[],[f190,f54])).
% 1.65/0.73  fof(f190,plain,(
% 1.65/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.65/0.73    inference(superposition,[],[f67,f183])).
% 1.65/0.73  fof(f67,plain,(
% 1.65/0.73    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f30])).
% 1.65/0.73  fof(f30,plain,(
% 1.65/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.73    inference(flattening,[],[f29])).
% 1.65/0.73  fof(f29,plain,(
% 1.65/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.73    inference(ennf_transformation,[],[f22])).
% 1.65/0.73  fof(f22,axiom,(
% 1.65/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.65/0.73  fof(f482,plain,(
% 1.65/0.73    k1_xboole_0 = k1_tarski(sK0) | ~v4_relat_1(sK2,k1_xboole_0)),
% 1.65/0.73    inference(resolution,[],[f290,f201])).
% 1.65/0.73  fof(f201,plain,(
% 1.65/0.73    ( ! [X1] : (r1_tarski(k1_tarski(sK0),X1) | ~v4_relat_1(sK2,X1)) )),
% 1.65/0.73    inference(subsumption_resolution,[],[f194,f111])).
% 1.65/0.73  fof(f194,plain,(
% 1.65/0.73    ( ! [X1] : (r1_tarski(k1_tarski(sK0),X1) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 1.65/0.73    inference(superposition,[],[f72,f183])).
% 1.65/0.73  fof(f72,plain,(
% 1.65/0.73    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f47])).
% 1.65/0.73  fof(f47,plain,(
% 1.65/0.73    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(nnf_transformation,[],[f32])).
% 1.65/0.73  fof(f32,plain,(
% 1.65/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(ennf_transformation,[],[f11])).
% 1.65/0.73  fof(f11,axiom,(
% 1.65/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.65/0.73  fof(f290,plain,(
% 1.65/0.73    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 1.65/0.73    inference(subsumption_resolution,[],[f289,f111])).
% 1.65/0.73  fof(f289,plain,(
% 1.65/0.73    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2 | ~v1_relat_1(sK2)) )),
% 1.65/0.73    inference(subsumption_resolution,[],[f278,f258])).
% 1.65/0.73  fof(f258,plain,(
% 1.65/0.73    ( ! [X0] : (v5_relat_1(sK2,X0)) )),
% 1.65/0.73    inference(resolution,[],[f252,f132])).
% 1.65/0.73  fof(f132,plain,(
% 1.65/0.73    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X3,X2)) )),
% 1.65/0.73    inference(superposition,[],[f88,f99])).
% 1.65/0.73  fof(f99,plain,(
% 1.65/0.73    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.65/0.73    inference(equality_resolution,[],[f81])).
% 1.65/0.73  fof(f81,plain,(
% 1.65/0.73    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.65/0.73    inference(cnf_transformation,[],[f52])).
% 1.65/0.73  fof(f88,plain,(
% 1.65/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f39])).
% 1.65/0.73  fof(f278,plain,(
% 1.65/0.73    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2 | ~v5_relat_1(sK2,X2) | ~v1_relat_1(sK2)) )),
% 1.65/0.73    inference(superposition,[],[f123,f244])).
% 1.65/0.73  fof(f123,plain,(
% 1.65/0.73    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.65/0.73    inference(resolution,[],[f79,f70])).
% 1.65/0.73  fof(f70,plain,(
% 1.65/0.73    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f46])).
% 1.65/0.73  fof(f46,plain,(
% 1.65/0.73    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(nnf_transformation,[],[f31])).
% 1.65/0.73  fof(f31,plain,(
% 1.65/0.73    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.65/0.73    inference(ennf_transformation,[],[f12])).
% 1.65/0.73  fof(f12,axiom,(
% 1.65/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.65/0.73  fof(f79,plain,(
% 1.65/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.65/0.73    inference(cnf_transformation,[],[f50])).
% 1.65/0.73  fof(f50,plain,(
% 1.65/0.73    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.73    inference(flattening,[],[f49])).
% 1.65/0.73  % (16099)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.65/0.73  fof(f49,plain,(
% 1.65/0.73    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.73    inference(nnf_transformation,[],[f2])).
% 1.65/0.73  fof(f2,axiom,(
% 1.65/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.73  fof(f60,plain,(
% 1.65/0.73    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.65/0.73    inference(cnf_transformation,[],[f6])).
% 1.65/0.73  fof(f6,axiom,(
% 1.65/0.73    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.65/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.65/0.73  % SZS output end Proof for theBenchmark
% 1.65/0.73  % (16086)------------------------------
% 1.65/0.73  % (16086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.73  % (16086)Termination reason: Refutation
% 1.65/0.73  
% 1.65/0.73  % (16086)Memory used [KB]: 1918
% 1.65/0.73  % (16086)Time elapsed: 0.147 s
% 1.65/0.73  % (16086)------------------------------
% 1.65/0.73  % (16086)------------------------------
% 1.65/0.73  % (16101)Refutation not found, incomplete strategy% (16101)------------------------------
% 1.65/0.73  % (16101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.73  % (16101)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.73  
% 1.65/0.73  % (16101)Memory used [KB]: 10746
% 1.65/0.73  % (16101)Time elapsed: 0.144 s
% 1.65/0.73  % (16101)------------------------------
% 1.65/0.73  % (16101)------------------------------
% 1.65/0.73  % (16105)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.65/0.73  % (15886)Success in time 0.365 s
%------------------------------------------------------------------------------

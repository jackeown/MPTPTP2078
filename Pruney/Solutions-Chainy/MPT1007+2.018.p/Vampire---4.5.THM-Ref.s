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
% DateTime   : Thu Dec  3 13:03:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 900 expanded)
%              Number of leaves         :   22 ( 220 expanded)
%              Depth                    :   24
%              Number of atoms          :  336 (3402 expanded)
%              Number of equality atoms :   93 ( 726 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(resolution,[],[f236,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f236,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f235,f87])).

fof(f87,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f70,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f235,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tarski(sK0))
      | ~ m1_subset_1(X0,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f234,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f234,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f233,f160])).

fof(f160,plain,(
    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f52,f157])).

fof(f157,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f139,f156])).

fof(f156,plain,(
    k1_xboole_0 = k11_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f152,f91])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

% (15465)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f46,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f152,plain,
    ( k1_xboole_0 = k11_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f149,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f149,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f148,f55])).

fof(f55,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f147,f98])).

fof(f98,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f82,f53])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X1)
      | r2_hidden(k1_funct_1(sK2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f146,f91])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),X1)
      | ~ v5_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f76,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f139,plain,
    ( k1_xboole_0 != k11_relat_1(sK2,sK0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f137,f100])).

fof(f100,plain,(
    ! [X2] : k11_relat_1(sK2,X2) = k9_relat_1(sK2,k1_tarski(X2)) ),
    inference(resolution,[],[f64,f91])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f137,plain,
    ( k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f136,f91])).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f105,f108])).

fof(f108,plain,(
    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f106,plain,
    ( sK2 = k7_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f96])).

fof(f96,plain,(
    v4_relat_1(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f81,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | k1_xboole_0 = k7_relat_1(sK2,X0)
      | k1_xboole_0 != k9_relat_1(sK2,X0) ) ),
    inference(superposition,[],[f63,f103])).

fof(f103,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f72,f91])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f52,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ) ),
    inference(subsumption_resolution,[],[f232,f155])).

fof(f155,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f55,f151])).

fof(f151,plain,(
    k1_xboole_0 = k1_funct_1(sK2,sK0) ),
    inference(resolution,[],[f149,f133])).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f132,f91])).

fof(f132,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f84,f51])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_xboole_0,sK1)
      | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ) ),
    inference(subsumption_resolution,[],[f231,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f231,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(k1_xboole_0,sK1)
      | ~ v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1) ) ),
    inference(resolution,[],[f230,f161])).

fof(f161,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(backward_demodulation,[],[f53,f157])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_xboole_0,X0)
      | ~ v1_funct_2(k1_xboole_0,X2,X0) ) ),
    inference(forward_demodulation,[],[f229,f187])).

fof(f187,plain,(
    ! [X0] : k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f186,f129])).

fof(f129,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f128,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f127,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f126,f57])).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f73,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f122,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f121,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,(
    ! [X0] :
      ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
      | r2_hidden(X0,k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f119,f61])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f74,f57])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f186,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f185,f57])).

fof(f185,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f170,f157])).

fof(f170,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)
      | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f133,f157])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(k1_xboole_0,X2,X0)
      | r2_hidden(k1_funct_1(k1_xboole_0,X1),X0) ) ),
    inference(resolution,[],[f83,f159])).

fof(f159,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f157])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
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
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (15464)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (15456)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (15448)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (15445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (15441)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (15457)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (15448)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(resolution,[],[f236,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f235,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.52    inference(superposition,[],[f70,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(k1_tarski(sK0)) | ~m1_subset_1(X0,k1_tarski(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f234,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f233,f160])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f52,f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    k1_xboole_0 = sK2),
% 0.20/0.52    inference(subsumption_resolution,[],[f139,f156])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK2,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f152,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f80,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  % (15465)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f22])).
% 0.20/0.52  fof(f22,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f149,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.52    inference(resolution,[],[f148,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.52    inference(resolution,[],[f147,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    v5_relat_1(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f82,f53])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f146,f91])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),X1) | ~v5_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 0.20/0.52    inference(resolution,[],[f76,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK2,sK0) | k1_xboole_0 = sK2),
% 0.20/0.52    inference(superposition,[],[f137,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X2] : (k11_relat_1(sK2,X2) = k9_relat_1(sK2,k1_tarski(X2))) )),
% 0.20/0.52    inference(resolution,[],[f64,f91])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0)) | k1_xboole_0 = sK2),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f91])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 != k9_relat_1(sK2,k1_tarski(sK0))),
% 0.20/0.52    inference(superposition,[],[f105,f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    sK2 = k7_relat_1(sK2,k1_tarski(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f91])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    sK2 = k7_relat_1(sK2,k1_tarski(sK0)) | ~v1_relat_1(sK2)),
% 0.20/0.52    inference(resolution,[],[f77,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    v4_relat_1(sK2,k1_tarski(sK0))),
% 0.20/0.52    inference(resolution,[],[f81,f53])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK2,X0)) | k1_xboole_0 = k7_relat_1(sK2,X0) | k1_xboole_0 != k9_relat_1(sK2,X0)) )),
% 0.20/0.52    inference(superposition,[],[f63,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.20/0.52    inference(resolution,[],[f72,f91])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f232,f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ~r2_hidden(k1_xboole_0,sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f55,f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    k1_xboole_0 = k1_funct_1(sK2,sK0)),
% 0.20/0.52    inference(resolution,[],[f149,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k1_funct_1(sK2,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f91])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k1_funct_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.52    inference(resolution,[],[f84,f51])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f231,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    k1_xboole_0 != sK1),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(k1_xboole_0,sK1) | ~v1_funct_2(k1_xboole_0,k1_tarski(sK0),sK1)) )),
% 0.20/0.52    inference(resolution,[],[f230,f161])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.20/0.52    inference(backward_demodulation,[],[f53,f157])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_xboole_0,X0) | ~v1_funct_2(k1_xboole_0,X2,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f229,f187])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f186,f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f128,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f127,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f126,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f73,f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f122,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f121,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f120,f56])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) | r2_hidden(X0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f119,f61])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) | r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f74,f57])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f185,f57])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f170,f157])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) | r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.52    inference(backward_demodulation,[],[f133,f157])).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(k1_xboole_0,X2,X0) | r2_hidden(k1_funct_1(k1_xboole_0,X1),X0)) )),
% 0.20/0.52    inference(resolution,[],[f83,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    v1_funct_1(k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f51,f157])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15448)------------------------------
% 0.20/0.52  % (15448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15448)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15448)Memory used [KB]: 6396
% 0.20/0.52  % (15448)Time elapsed: 0.072 s
% 0.20/0.52  % (15448)------------------------------
% 0.20/0.52  % (15448)------------------------------
% 0.20/0.52  % (15444)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (15453)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (15458)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.53  % (15440)Success in time 0.17 s
%------------------------------------------------------------------------------

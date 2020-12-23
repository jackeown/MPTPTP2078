%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:23 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 213 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  335 ( 817 expanded)
%              Number of equality atoms :  175 ( 372 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f180,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f48,f163])).

fof(f163,plain,(
    k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k11_relat_1(sK4,sK2) != k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( k11_relat_1(sK4,sK2) != k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f157,f152])).

fof(f152,plain,
    ( k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f149,f101])).

fof(f101,plain,(
    ! [X0] : k11_relat_1(sK4,X0) = k9_relat_1(sK4,k2_tarski(X0,X0)) ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f100,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f98,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_tarski(sK2,sK2),sK3))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f77,f71])).

fof(f71,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f47,f75])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f35])).

% (30533)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f35,plain,
    ( k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f149,plain,
    ( k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k9_relat_1(sK4,k2_tarski(sK2,sK2))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f116,f145])).

fof(f145,plain,
    ( k2_tarski(sK2,sK2) = k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f103,f78])).

fof(f78,plain,(
    v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f46,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,
    ( ~ v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3)
    | k1_xboole_0 = sK3
    | k2_tarski(sK2,sK2) = k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3) ),
    inference(resolution,[],[f90,f77])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK4,X1,X0)
      | k8_relset_1(X1,X0,sK4,X0) = X1 ) ),
    inference(resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k9_relat_1(sK4,k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3)) ),
    inference(superposition,[],[f96,f93])).

fof(f93,plain,(
    ! [X0] : k7_relset_1(k2_tarski(sK2,sK2),sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f96,plain,(
    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k7_relset_1(k2_tarski(sK2,sK2),sK3,sK4,k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3)) ),
    inference(resolution,[],[f77,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f157,plain,
    ( k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) != k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f76,f144])).

fof(f144,plain,
    ( k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f126,f100])).

fof(f126,plain,
    ( ~ v1_relat_1(sK4)
    | k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f121,f92])).

fof(f92,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK4))
      | k11_relat_1(sK4,X3) = k2_tarski(k1_funct_1(sK4,X3),k1_funct_1(sK4,X3))
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f45,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f121,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f113,f87])).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

% (30524)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f113,plain,
    ( sP1(sK2,sK2,k1_relat_1(sK4))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f88,f105])).

fof(f105,plain,
    ( k2_tarski(sK2,sK2) = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f104,f78])).

fof(f104,plain,
    ( ~ v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3)
    | k2_tarski(sK2,sK2) = k1_relat_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f99,f94])).

fof(f94,plain,(
    k1_relat_1(sK4) = k1_relset_1(k2_tarski(sK2,sK2),sK3,sK4) ),
    inference(resolution,[],[f77,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f99,plain,
    ( ~ v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3)
    | k1_xboole_0 = sK3
    | k2_tarski(sK2,sK2) = k1_relset_1(k2_tarski(sK2,sK2),sK3,sK4) ),
    inference(resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f95,plain,(
    sP0(k2_tarski(sK2,sK2),sK4,sK3) ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f30])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f88,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f76,plain,(
    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) != k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
    inference(definition_unfolding,[],[f49,f75,f75])).

fof(f49,plain,(
    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (30512)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.53  % (30515)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.53  % (30511)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  % (30512)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % (30530)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f180,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(trivial_inequality_removal,[],[f179])).
% 1.28/0.54  fof(f179,plain,(
% 1.28/0.54    k1_xboole_0 != k1_xboole_0),
% 1.28/0.54    inference(superposition,[],[f48,f163])).
% 1.28/0.54  fof(f163,plain,(
% 1.28/0.54    k1_xboole_0 = sK3),
% 1.28/0.54    inference(trivial_inequality_removal,[],[f162])).
% 1.28/0.54  fof(f162,plain,(
% 1.28/0.54    k11_relat_1(sK4,sK2) != k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f161])).
% 1.28/0.54  fof(f161,plain,(
% 1.28/0.54    k11_relat_1(sK4,sK2) != k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 1.28/0.54    inference(superposition,[],[f157,f152])).
% 1.28/0.54  fof(f152,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(forward_demodulation,[],[f149,f101])).
% 1.28/0.54  fof(f101,plain,(
% 1.28/0.54    ( ! [X0] : (k11_relat_1(sK4,X0) = k9_relat_1(sK4,k2_tarski(X0,X0))) )),
% 1.28/0.54    inference(resolution,[],[f100,f80])).
% 1.28/0.54  fof(f80,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))) )),
% 1.28/0.54    inference(definition_unfolding,[],[f60,f75])).
% 1.28/0.54  fof(f75,plain,(
% 1.28/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f24])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.28/0.54  fof(f100,plain,(
% 1.28/0.54    v1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f98,f70])).
% 1.28/0.54  fof(f70,plain,(
% 1.28/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.28/0.54  fof(f98,plain,(
% 1.28/0.54    ~v1_relat_1(k2_zfmisc_1(k2_tarski(sK2,sK2),sK3)) | v1_relat_1(sK4)),
% 1.28/0.54    inference(resolution,[],[f77,f71])).
% 1.28/0.54  fof(f71,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.28/0.54  fof(f77,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK2,sK2),sK3)))),
% 1.28/0.54    inference(definition_unfolding,[],[f47,f75])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  % (30533)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.54  fof(f35,plain,(
% 1.28/0.54    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2)) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.28/0.54    inference(flattening,[],[f17])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.28/0.54    inference(ennf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.28/0.54    inference(negated_conjecture,[],[f15])).
% 1.28/0.54  fof(f15,conjecture,(
% 1.28/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.28/0.54  fof(f149,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k9_relat_1(sK4,k2_tarski(sK2,sK2)) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(superposition,[],[f116,f145])).
% 1.28/0.54  fof(f145,plain,(
% 1.28/0.54    k2_tarski(sK2,sK2) = k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(resolution,[],[f103,f78])).
% 1.28/0.54  fof(f78,plain,(
% 1.28/0.54    v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3)),
% 1.28/0.54    inference(definition_unfolding,[],[f46,f75])).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  fof(f103,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3) | k1_xboole_0 = sK3 | k2_tarski(sK2,sK2) = k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3)),
% 1.28/0.54    inference(resolution,[],[f90,f77])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK4,X1,X0) | k8_relset_1(X1,X0,sK4,X0) = X1) )),
% 1.28/0.54    inference(resolution,[],[f45,f73])).
% 1.28/0.54  fof(f73,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.28/0.54    inference(flattening,[],[f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.28/0.54    inference(ennf_transformation,[],[f14])).
% 1.28/0.54  fof(f14,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    v1_funct_1(sK4)),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  fof(f116,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k9_relat_1(sK4,k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3))),
% 1.28/0.54    inference(superposition,[],[f96,f93])).
% 1.28/0.54  fof(f93,plain,(
% 1.28/0.54    ( ! [X0] : (k7_relset_1(k2_tarski(sK2,sK2),sK3,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.28/0.54    inference(resolution,[],[f77,f72])).
% 1.28/0.54  fof(f72,plain,(
% 1.28/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f11])).
% 1.28/0.54  fof(f11,axiom,(
% 1.28/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.28/0.54  fof(f96,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) = k7_relset_1(k2_tarski(sK2,sK2),sK3,sK4,k8_relset_1(k2_tarski(sK2,sK2),sK3,sK4,sK3))),
% 1.28/0.54    inference(resolution,[],[f77,f51])).
% 1.28/0.54  fof(f51,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.28/0.54    inference(ennf_transformation,[],[f12])).
% 1.28/0.54  fof(f12,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.28/0.54  fof(f157,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) != k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(superposition,[],[f76,f144])).
% 1.28/0.54  fof(f144,plain,(
% 1.28/0.54    k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(resolution,[],[f126,f100])).
% 1.28/0.54  fof(f126,plain,(
% 1.28/0.54    ~v1_relat_1(sK4) | k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(resolution,[],[f121,f92])).
% 1.28/0.54  fof(f92,plain,(
% 1.28/0.54    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK4)) | k11_relat_1(sK4,X3) = k2_tarski(k1_funct_1(sK4,X3),k1_funct_1(sK4,X3)) | ~v1_relat_1(sK4)) )),
% 1.28/0.54    inference(resolution,[],[f45,f79])).
% 1.28/0.54  fof(f79,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k2_tarski(k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(definition_unfolding,[],[f50,f75])).
% 1.28/0.54  fof(f50,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(flattening,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.54    inference(ennf_transformation,[],[f9])).
% 1.28/0.54  fof(f9,axiom,(
% 1.28/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 1.28/0.54  fof(f121,plain,(
% 1.28/0.54    r2_hidden(sK2,k1_relat_1(sK4)) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(resolution,[],[f113,f87])).
% 1.28/0.54  fof(f87,plain,(
% 1.28/0.54    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.28/0.54    inference(equality_resolution,[],[f62])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f43])).
% 1.28/0.54  % (30524)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.28/0.54  fof(f43,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.28/0.54    inference(rectify,[],[f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.28/0.54    inference(flattening,[],[f39])).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 1.28/0.54    inference(nnf_transformation,[],[f32])).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.28/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.28/0.54  fof(f113,plain,(
% 1.28/0.54    sP1(sK2,sK2,k1_relat_1(sK4)) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(superposition,[],[f88,f105])).
% 1.28/0.54  fof(f105,plain,(
% 1.28/0.54    k2_tarski(sK2,sK2) = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(resolution,[],[f104,f78])).
% 1.28/0.54  fof(f104,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3) | k2_tarski(sK2,sK2) = k1_relat_1(sK4) | k1_xboole_0 = sK3),
% 1.28/0.54    inference(forward_demodulation,[],[f99,f94])).
% 1.28/0.54  fof(f94,plain,(
% 1.28/0.54    k1_relat_1(sK4) = k1_relset_1(k2_tarski(sK2,sK2),sK3,sK4)),
% 1.28/0.54    inference(resolution,[],[f77,f69])).
% 1.28/0.54  fof(f69,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.54  fof(f99,plain,(
% 1.28/0.54    ~v1_funct_2(sK4,k2_tarski(sK2,sK2),sK3) | k1_xboole_0 = sK3 | k2_tarski(sK2,sK2) = k1_relset_1(k2_tarski(sK2,sK2),sK3,sK4)),
% 1.28/0.54    inference(resolution,[],[f95,f53])).
% 1.28/0.54  fof(f53,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f37])).
% 1.28/0.54  fof(f37,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.28/0.54    inference(rectify,[],[f36])).
% 1.28/0.54  fof(f36,plain,(
% 1.28/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.54    inference(nnf_transformation,[],[f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.28/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.28/0.54  fof(f95,plain,(
% 1.28/0.54    sP0(k2_tarski(sK2,sK2),sK4,sK3)),
% 1.28/0.54    inference(resolution,[],[f77,f57])).
% 1.28/0.54  fof(f57,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f38])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(nnf_transformation,[],[f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(definition_folding,[],[f23,f30])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(flattening,[],[f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f13])).
% 1.28/0.54  fof(f13,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.28/0.54  fof(f88,plain,(
% 1.28/0.54    ( ! [X0,X1] : (sP1(X1,X0,k2_tarski(X0,X1))) )),
% 1.28/0.54    inference(equality_resolution,[],[f67])).
% 1.28/0.54  fof(f67,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.28/0.54    inference(cnf_transformation,[],[f44])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.28/0.54    inference(nnf_transformation,[],[f33])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 1.28/0.54    inference(definition_folding,[],[f1,f32])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.28/0.54  fof(f76,plain,(
% 1.28/0.54    k2_relset_1(k2_tarski(sK2,sK2),sK3,sK4) != k2_tarski(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2))),
% 1.28/0.54    inference(definition_unfolding,[],[f49,f75,f75])).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    k2_relset_1(k1_tarski(sK2),sK3,sK4) != k1_tarski(k1_funct_1(sK4,sK2))),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    k1_xboole_0 != sK3),
% 1.28/0.54    inference(cnf_transformation,[],[f35])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (30512)------------------------------
% 1.28/0.54  % (30512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (30512)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (30512)Memory used [KB]: 1791
% 1.28/0.54  % (30512)Time elapsed: 0.117 s
% 1.28/0.54  % (30512)------------------------------
% 1.28/0.54  % (30512)------------------------------
% 1.28/0.54  % (30519)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.28/0.54  % (30535)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.28/0.54  % (30525)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.54  % (30516)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % (30510)Success in time 0.176 s
%------------------------------------------------------------------------------

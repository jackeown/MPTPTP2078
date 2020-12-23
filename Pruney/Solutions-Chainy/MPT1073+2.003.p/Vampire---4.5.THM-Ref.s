%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 238 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  197 ( 867 expanded)
%              Number of equality atoms :   62 ( 192 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f162,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f162,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f156,f127])).

fof(f127,plain,(
    ~ sP5(sK3) ),
    inference(resolution,[],[f115,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f69,f78_D])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f78_D])).

fof(f78_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f115,plain,(
    r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(sK3),sK3),sK0),sK3) ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,(
    r2_hidden(sK0,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f41,f86])).

fof(f86,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f41,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK4(X1,k1_relat_1(sK3),sK3),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f85,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f97,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(k4_tarski(sK4(X1,k1_relat_1(sK3),sK3),X1),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f61,f91])).

fof(f91,plain,(
    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f156,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))
    | sP5(sK3) ),
    inference(backward_demodulation,[],[f87,f150])).

fof(f150,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f149,f143])).

fof(f143,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f132,f94])).

fof(f94,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f83,f81])).

fof(f81,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f40,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f132,plain,(
    sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) ),
    inference(subsumption_resolution,[],[f131,f85])).

fof(f131,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f149,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3)) ),
    inference(resolution,[],[f136,f37])).

fof(f37,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | sK0 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f136,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f117,f94])).

fof(f117,plain,(
    m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f112,plain,(
    r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ),
    inference(resolution,[],[f99,f88])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(sK4(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f96,f85])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK3))
      | r2_hidden(sK4(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f60,f91])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | sP5(sK3) ),
    inference(resolution,[],[f40,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:28:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (14546)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (14545)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (14554)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (14547)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (14552)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (14547)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f163,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(forward_demodulation,[],[f162,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f156,f127])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    ~sP5(sK3)),
% 0.22/0.55    inference(resolution,[],[f115,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 0.22/0.55    inference(general_splitting,[],[f69,f78_D])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f78_D])).
% 0.22/0.55  fof(f78_D,plain,(
% 0.22/0.55    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.22/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    r2_hidden(k4_tarski(sK4(sK0,k1_relat_1(sK3),sK3),sK0),sK3)),
% 0.22/0.55    inference(resolution,[],[f100,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    r2_hidden(sK0,k2_relat_1(sK3))),
% 0.22/0.55    inference(backward_demodulation,[],[f41,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f40,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.55    inference(negated_conjecture,[],[f18])).
% 0.22/0.55  fof(f18,conjecture,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK4(X1,k1_relat_1(sK3),sK3),X1),sK3)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f97,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f40,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(k4_tarski(sK4(X1,k1_relat_1(sK3),sK3),X1),sK3) | ~v1_relat_1(sK3)) )),
% 0.22/0.55    inference(superposition,[],[f61,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))),
% 0.22/0.55    inference(resolution,[],[f85,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ~v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) | sP5(sK3)),
% 0.22/0.55    inference(backward_demodulation,[],[f87,f150])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    k1_xboole_0 = sK2),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    sK0 = k1_funct_1(sK3,sK4(sK0,sK1,sK3)) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f132,f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f83,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(subsumption_resolution,[],[f80,f40])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    inference(resolution,[],[f39,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f40,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f85])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f125,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ~v1_funct_1(sK3) | sK0 = k1_funct_1(sK3,sK4(sK0,k1_relat_1(sK3),sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f115,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | sK0 != k1_funct_1(sK3,sK4(sK0,sK1,sK3))),
% 0.22/0.55    inference(resolution,[],[f136,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X4] : (~m1_subset_1(X4,sK1) | sK0 != k1_funct_1(sK3,X4)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    m1_subset_1(sK4(sK0,sK1,sK3),sK1) | k1_xboole_0 = sK2),
% 0.22/0.55    inference(superposition,[],[f117,f94])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    m1_subset_1(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))),
% 0.22/0.55    inference(resolution,[],[f112,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    r2_hidden(sK4(sK0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))),
% 0.22/0.55    inference(resolution,[],[f99,f88])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK4(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f96,f85])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(sK4(X0,k1_relat_1(sK3),sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.22/0.55    inference(superposition,[],[f60,f91])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | sP5(sK3)),
% 0.22/0.55    inference(resolution,[],[f40,f78])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (14547)------------------------------
% 0.22/0.55  % (14547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14547)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (14547)Memory used [KB]: 6268
% 0.22/0.55  % (14547)Time elapsed: 0.109 s
% 0.22/0.55  % (14547)------------------------------
% 0.22/0.55  % (14547)------------------------------
% 0.22/0.55  % (14541)Success in time 0.186 s
%------------------------------------------------------------------------------

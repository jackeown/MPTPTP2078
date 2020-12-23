%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  123 (35748 expanded)
%              Number of leaves         :    7 (6808 expanded)
%              Depth                    :   50
%              Number of atoms          :  431 (183511 expanded)
%              Number of equality atoms :  144 (33803 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f411,f225])).

fof(f225,plain,(
    v4_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f78,f219])).

fof(f219,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f218,f78])).

fof(f218,plain,
    ( k1_xboole_0 = sK0
    | ~ v4_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f217,f81])).

fof(f81,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

fof(f217,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f215,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f215,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f210,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f60,f65])).

fof(f65,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f59,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f23,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f23,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f210,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f209,f184])).

fof(f184,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f181,f162])).

fof(f162,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f161,f78])).

fof(f161,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f156,f105])).

fof(f156,plain,
    ( ~ v4_relat_1(sK1,k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f154,f81])).

fof(f154,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f136,f31])).

fof(f136,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f135,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f135,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f134,f66])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f24,f32])).

fof(f134,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f133,f25])).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f133,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f132,f81])).

fof(f132,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(f20,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f181,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f180,f20])).

fof(f180,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f179,f78])).

% (31152)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f179,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f176,f105])).

fof(f176,plain,
    ( ~ v4_relat_1(sK1,k1_relat_1(sK2))
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f174,f81])).

fof(f174,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f172,f31])).

fof(f172,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f171,f66])).

fof(f171,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f139,f22])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r1_partfun1(sK1,sK2)
      | ~ v1_relat_1(X0)
      | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f138,f25])).

fof(f138,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f137,f81])).

fof(f137,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0))
      | r1_partfun1(sK1,sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | r1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f21,f80])).

fof(f80,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f26,f33])).

fof(f21,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f209,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f208,f22])).

fof(f208,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f207,f66])).

fof(f207,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f190,f188])).

fof(f188,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f186,f184])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f185,f83])).

fof(f185,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f182,f153])).

fof(f153,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f152,f78])).

fof(f152,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f149,f105])).

fof(f149,plain,
    ( ~ v4_relat_1(sK1,k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f147,f81])).

fof(f147,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f98,f31])).

fof(f98,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f97,f22])).

fof(f97,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f96,f66])).

fof(f96,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f95,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f94,f81])).

fof(f94,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(resolution,[],[f82,f29])).

fof(f82,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f19,f80])).

fof(f19,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f182,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_xboole_0 = sK0
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f180,f82])).

fof(f190,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK1,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f189,f25])).

fof(f189,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | ~ r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f187,f81])).

fof(f187,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | ~ r1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f185,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f411,plain,(
    ~ v4_relat_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f405,f81])).

fof(f405,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f398,f31])).

fof(f398,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f397,f248])).

fof(f248,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f224,f247])).

fof(f247,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f239,f221])).

fof(f221,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f24,f219])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f220,f42])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f220,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f23,f219])).

fof(f224,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f65,f219])).

fof(f397,plain,(
    ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f396,f66])).

fof(f396,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f395,f346])).

fof(f346,plain,(
    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f343,f256])).

fof(f256,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f252,f225])).

fof(f252,plain,
    ( ~ v4_relat_1(sK1,k1_xboole_0)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f156,f248])).

fof(f343,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f257,f20])).

fof(f257,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f254,f225])).

fof(f254,plain,
    ( ~ v4_relat_1(sK1,k1_xboole_0)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(backward_demodulation,[],[f176,f248])).

fof(f395,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f390,f22])).

fof(f390,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f352,f350])).

fof(f350,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f348,f346])).

fof(f348,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f347,f83])).

fof(f347,plain,(
    r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f344,f255])).

fof(f255,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f251,f225])).

fof(f251,plain,
    ( ~ v4_relat_1(sK1,k1_xboole_0)
    | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f149,f248])).

fof(f344,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f257,f82])).

fof(f352,plain,(
    ! [X0] :
      ( ~ r1_partfun1(sK1,X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f351,f25])).

fof(f351,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | ~ r1_partfun1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f349,f81])).

fof(f349,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(X0))
      | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3)
      | ~ r1_partfun1(sK1,X0) ) ),
    inference(resolution,[],[f347,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (819068929)
% 0.20/0.37  ipcrm: permission denied for id (819134467)
% 0.20/0.39  ipcrm: permission denied for id (819232783)
% 0.20/0.41  ipcrm: permission denied for id (819331103)
% 0.20/0.41  ipcrm: permission denied for id (819363874)
% 0.20/0.41  ipcrm: permission denied for id (819396644)
% 0.20/0.44  ipcrm: permission denied for id (819560507)
% 0.20/0.45  ipcrm: permission denied for id (819626057)
% 0.20/0.46  ipcrm: permission denied for id (819658830)
% 0.20/0.46  ipcrm: permission denied for id (819691600)
% 0.20/0.48  ipcrm: permission denied for id (819724379)
% 0.20/0.48  ipcrm: permission denied for id (819757151)
% 0.20/0.49  ipcrm: permission denied for id (819789928)
% 0.20/0.50  ipcrm: permission denied for id (819822703)
% 0.69/0.63  % (31163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.69/0.63  % (31158)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.69/0.63  % (31166)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.69/0.63  % (31156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.69/0.64  % (31164)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.69/0.64  % (31163)Refutation found. Thanks to Tanya!
% 0.69/0.64  % SZS status Theorem for theBenchmark
% 0.69/0.64  % SZS output start Proof for theBenchmark
% 0.69/0.64  fof(f412,plain,(
% 0.69/0.64    $false),
% 0.69/0.64    inference(subsumption_resolution,[],[f411,f225])).
% 0.69/0.64  fof(f225,plain,(
% 0.69/0.64    v4_relat_1(sK1,k1_xboole_0)),
% 0.69/0.64    inference(backward_demodulation,[],[f78,f219])).
% 0.69/0.64  fof(f219,plain,(
% 0.69/0.64    k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f218,f78])).
% 0.69/0.64  fof(f218,plain,(
% 0.69/0.64    k1_xboole_0 = sK0 | ~v4_relat_1(sK1,sK0)),
% 0.69/0.64    inference(subsumption_resolution,[],[f217,f81])).
% 0.69/0.64  fof(f81,plain,(
% 0.69/0.64    v1_relat_1(sK1)),
% 0.69/0.64    inference(resolution,[],[f26,f32])).
% 0.69/0.64  fof(f32,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f14])).
% 0.69/0.64  fof(f14,plain,(
% 0.69/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.69/0.64    inference(ennf_transformation,[],[f2])).
% 0.69/0.64  fof(f2,axiom,(
% 0.69/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.69/0.64  fof(f26,plain,(
% 0.69/0.64    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f10,plain,(
% 0.69/0.64    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1))),
% 0.69/0.64    inference(flattening,[],[f9])).
% 0.69/0.64  fof(f9,plain,(
% 0.69/0.64    ? [X0,X1] : (? [X2] : ((r1_partfun1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relset_1(X0,X0,X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)))),
% 0.69/0.64    inference(ennf_transformation,[],[f8])).
% 0.69/0.64  fof(f8,negated_conjecture,(
% 0.69/0.64    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.69/0.64    inference(negated_conjecture,[],[f7])).
% 0.69/0.64  fof(f7,conjecture,(
% 0.69/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) <=> ! [X3] : (r2_hidden(X3,k1_relset_1(X0,X0,X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)))))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).
% 0.69/0.64  fof(f217,plain,(
% 0.69/0.64    k1_xboole_0 = sK0 | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0)),
% 0.69/0.64    inference(resolution,[],[f215,f31])).
% 0.69/0.64  fof(f31,plain,(
% 0.69/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f13])).
% 0.69/0.64  fof(f13,plain,(
% 0.69/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.69/0.64    inference(ennf_transformation,[],[f1])).
% 0.69/0.64  fof(f1,axiom,(
% 0.69/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.69/0.64  fof(f215,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(duplicate_literal_removal,[],[f214])).
% 0.69/0.64  fof(f214,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.69/0.64    inference(superposition,[],[f210,f105])).
% 0.69/0.64  fof(f105,plain,(
% 0.69/0.64    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(superposition,[],[f60,f65])).
% 0.69/0.64  fof(f65,plain,(
% 0.69/0.64    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 0.69/0.64    inference(resolution,[],[f24,f33])).
% 0.69/0.64  fof(f33,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f15])).
% 0.69/0.64  fof(f15,plain,(
% 0.69/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.69/0.64    inference(ennf_transformation,[],[f4])).
% 0.69/0.64  fof(f4,axiom,(
% 0.69/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.69/0.64  fof(f24,plain,(
% 0.69/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f60,plain,(
% 0.69/0.64    sK0 = k1_relset_1(sK0,sK0,sK2) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f59,f24])).
% 0.69/0.64  fof(f59,plain,(
% 0.69/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 0.69/0.64    inference(resolution,[],[f23,f41])).
% 0.69/0.64  fof(f41,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f18])).
% 0.69/0.64  fof(f18,plain,(
% 0.69/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.69/0.64    inference(flattening,[],[f17])).
% 0.69/0.64  fof(f17,plain,(
% 0.69/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.69/0.64    inference(ennf_transformation,[],[f5])).
% 0.69/0.64  fof(f5,axiom,(
% 0.69/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.69/0.64  fof(f23,plain,(
% 0.69/0.64    v1_funct_2(sK2,sK0,sK0)),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f210,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f209,f184])).
% 0.69/0.64  fof(f184,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f181,f162])).
% 0.69/0.64  fof(f162,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f161,f78])).
% 0.69/0.64  fof(f161,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,sK0) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(superposition,[],[f156,f105])).
% 0.69/0.64  fof(f156,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(subsumption_resolution,[],[f154,f81])).
% 0.69/0.64  fof(f154,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,k1_relat_1(sK2))),
% 0.69/0.64    inference(resolution,[],[f136,f31])).
% 0.69/0.64  fof(f136,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f135,f22])).
% 0.69/0.64  fof(f22,plain,(
% 0.69/0.64    v1_funct_1(sK2)),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f135,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f134,f66])).
% 0.69/0.64  fof(f66,plain,(
% 0.69/0.64    v1_relat_1(sK2)),
% 0.69/0.64    inference(resolution,[],[f24,f32])).
% 0.69/0.64  fof(f134,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f133,f25])).
% 0.69/0.64  fof(f25,plain,(
% 0.69/0.64    v1_funct_1(sK1)),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f133,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f132,f81])).
% 0.69/0.64  fof(f132,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(resolution,[],[f20,f29])).
% 0.69/0.64  fof(f29,plain,(
% 0.69/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | r1_partfun1(X0,X1)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f12])).
% 0.69/0.64  fof(f12,plain,(
% 0.69/0.64    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.69/0.64    inference(flattening,[],[f11])).
% 0.69/0.64  fof(f11,plain,(
% 0.69/0.64    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.69/0.64    inference(ennf_transformation,[],[f6])).
% 0.69/0.64  fof(f6,axiom,(
% 0.69/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 0.69/0.64  fof(f20,plain,(
% 0.69/0.64    ~r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f181,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(resolution,[],[f180,f20])).
% 0.69/0.64  fof(f180,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f179,f78])).
% 0.69/0.64  % (31152)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.69/0.64  fof(f179,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,sK0) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(superposition,[],[f176,f105])).
% 0.69/0.64  fof(f176,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_relat_1(sK2)) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f174,f81])).
% 0.69/0.64  fof(f174,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,k1_relat_1(sK2))),
% 0.69/0.64    inference(resolution,[],[f172,f31])).
% 0.69/0.64  fof(f172,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(subsumption_resolution,[],[f171,f66])).
% 0.69/0.64  fof(f171,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))),
% 0.69/0.64    inference(duplicate_literal_removal,[],[f169])).
% 0.69/0.64  fof(f169,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(resolution,[],[f139,f22])).
% 0.69/0.64  fof(f139,plain,(
% 0.69/0.64    ( ! [X0] : (~v1_funct_1(X0) | r1_partfun1(sK1,sK2) | ~v1_relat_1(X0) | k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f138,f25])).
% 0.69/0.64  fof(f138,plain,(
% 0.69/0.64    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f137,f81])).
% 0.69/0.64  fof(f137,plain,(
% 0.69/0.64    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = k1_funct_1(sK2,sK4(sK1,X0)) | r1_partfun1(sK1,sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(resolution,[],[f83,f28])).
% 0.69/0.64  fof(f28,plain,(
% 0.69/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f12])).
% 0.69/0.64  fof(f83,plain,(
% 0.69/0.64    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | r1_partfun1(sK1,sK2)) )),
% 0.69/0.64    inference(backward_demodulation,[],[f21,f80])).
% 0.69/0.64  fof(f80,plain,(
% 0.69/0.64    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.69/0.64    inference(resolution,[],[f26,f33])).
% 0.69/0.64  fof(f21,plain,(
% 0.69/0.64    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) | r1_partfun1(sK1,sK2)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f209,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f208,f22])).
% 0.69/0.64  fof(f208,plain,(
% 0.69/0.64    ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f207,f66])).
% 0.69/0.64  fof(f207,plain,(
% 0.69/0.64    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(duplicate_literal_removal,[],[f201])).
% 0.69/0.64  fof(f201,plain,(
% 0.69/0.64    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.69/0.64    inference(resolution,[],[f190,f188])).
% 0.69/0.64  fof(f188,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f186,f184])).
% 0.69/0.64  fof(f186,plain,(
% 0.69/0.64    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(resolution,[],[f185,f83])).
% 0.69/0.64  fof(f185,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f182,f153])).
% 0.69/0.64  fof(f153,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(subsumption_resolution,[],[f152,f78])).
% 0.69/0.64  fof(f152,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,sK0) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1)) | k1_xboole_0 = sK0),
% 0.69/0.64    inference(superposition,[],[f149,f105])).
% 0.69/0.64  fof(f149,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(subsumption_resolution,[],[f147,f81])).
% 0.69/0.64  fof(f147,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,k1_relat_1(sK2))),
% 0.69/0.64    inference(resolution,[],[f98,f31])).
% 0.69/0.64  fof(f98,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | r2_hidden(sK3,k1_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f97,f22])).
% 0.69/0.64  fof(f97,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f96,f66])).
% 0.69/0.64  fof(f96,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f95,f25])).
% 0.69/0.64  fof(f95,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f94,f81])).
% 0.69/0.64  fof(f94,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(resolution,[],[f82,f29])).
% 0.69/0.64  fof(f82,plain,(
% 0.69/0.64    ~r1_partfun1(sK1,sK2) | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(backward_demodulation,[],[f19,f80])).
% 0.69/0.64  fof(f19,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) | ~r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(cnf_transformation,[],[f10])).
% 0.69/0.64  fof(f182,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_xboole_0 = sK0 | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(resolution,[],[f180,f82])).
% 0.69/0.64  fof(f190,plain,(
% 0.69/0.64    ( ! [X0] : (~r1_partfun1(sK1,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | k1_xboole_0 = sK0) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f189,f25])).
% 0.69/0.64  fof(f189,plain,(
% 0.69/0.64    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | ~r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f187,f81])).
% 0.69/0.64  fof(f187,plain,(
% 0.69/0.64    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | ~r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(resolution,[],[f185,f27])).
% 0.69/0.64  fof(f27,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_partfun1(X0,X1)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f12])).
% 0.69/0.64  fof(f78,plain,(
% 0.69/0.64    v4_relat_1(sK1,sK0)),
% 0.69/0.64    inference(resolution,[],[f26,f34])).
% 0.69/0.64  fof(f34,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f16])).
% 0.69/0.64  fof(f16,plain,(
% 0.69/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.69/0.64    inference(ennf_transformation,[],[f3])).
% 0.69/0.64  fof(f3,axiom,(
% 0.69/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.69/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.69/0.64  fof(f411,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_xboole_0)),
% 0.69/0.64    inference(subsumption_resolution,[],[f405,f81])).
% 0.69/0.64  fof(f405,plain,(
% 0.69/0.64    ~v1_relat_1(sK1) | ~v4_relat_1(sK1,k1_xboole_0)),
% 0.69/0.64    inference(resolution,[],[f398,f31])).
% 0.69/0.64  fof(f398,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.69/0.64    inference(forward_demodulation,[],[f397,f248])).
% 0.69/0.64  fof(f248,plain,(
% 0.69/0.64    k1_xboole_0 = k1_relat_1(sK2)),
% 0.69/0.64    inference(backward_demodulation,[],[f224,f247])).
% 0.69/0.64  fof(f247,plain,(
% 0.69/0.64    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.69/0.64    inference(subsumption_resolution,[],[f239,f221])).
% 0.69/0.64  fof(f221,plain,(
% 0.69/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.69/0.64    inference(backward_demodulation,[],[f24,f219])).
% 0.69/0.64  fof(f239,plain,(
% 0.69/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.69/0.64    inference(resolution,[],[f220,f42])).
% 0.69/0.64  fof(f42,plain,(
% 0.69/0.64    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.69/0.64    inference(equality_resolution,[],[f39])).
% 0.69/0.64  fof(f39,plain,(
% 0.69/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.69/0.64    inference(cnf_transformation,[],[f18])).
% 0.69/0.64  fof(f220,plain,(
% 0.69/0.64    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.69/0.64    inference(backward_demodulation,[],[f23,f219])).
% 0.69/0.64  fof(f224,plain,(
% 0.69/0.64    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.69/0.64    inference(backward_demodulation,[],[f65,f219])).
% 0.69/0.64  fof(f397,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f396,f66])).
% 0.69/0.64  fof(f396,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.69/0.64    inference(subsumption_resolution,[],[f395,f346])).
% 0.69/0.64  fof(f346,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(subsumption_resolution,[],[f343,f256])).
% 0.69/0.64  fof(f256,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(subsumption_resolution,[],[f252,f225])).
% 0.69/0.64  fof(f252,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_xboole_0) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(backward_demodulation,[],[f156,f248])).
% 0.69/0.64  fof(f343,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)),
% 0.69/0.64    inference(resolution,[],[f257,f20])).
% 0.69/0.64  fof(f257,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(subsumption_resolution,[],[f254,f225])).
% 0.69/0.64  fof(f254,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_xboole_0) | r1_partfun1(sK1,sK2) | k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.69/0.64    inference(backward_demodulation,[],[f176,f248])).
% 0.69/0.64  fof(f395,plain,(
% 0.69/0.64    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK2)),
% 0.69/0.64    inference(subsumption_resolution,[],[f390,f22])).
% 0.69/0.64  fof(f390,plain,(
% 0.69/0.64    ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | ~v1_relat_1(sK2)),
% 0.69/0.64    inference(resolution,[],[f352,f350])).
% 0.69/0.64  fof(f350,plain,(
% 0.69/0.64    r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(subsumption_resolution,[],[f348,f346])).
% 0.69/0.64  fof(f348,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3) | r1_partfun1(sK1,sK2)),
% 0.69/0.64    inference(resolution,[],[f347,f83])).
% 0.69/0.64  fof(f347,plain,(
% 0.69/0.64    r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(subsumption_resolution,[],[f344,f255])).
% 0.69/0.64  fof(f255,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(subsumption_resolution,[],[f251,f225])).
% 0.69/0.64  fof(f251,plain,(
% 0.69/0.64    ~v4_relat_1(sK1,k1_xboole_0) | k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(backward_demodulation,[],[f149,f248])).
% 0.69/0.64  fof(f344,plain,(
% 0.69/0.64    k1_funct_1(sK1,sK4(sK1,sK2)) = k1_funct_1(sK2,sK4(sK1,sK2)) | r2_hidden(sK3,k1_relat_1(sK1))),
% 0.69/0.64    inference(resolution,[],[f257,f82])).
% 0.69/0.64  fof(f352,plain,(
% 0.69/0.64    ( ! [X0] : (~r1_partfun1(sK1,X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | ~v1_relat_1(X0)) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f351,f25])).
% 0.69/0.64  fof(f351,plain,(
% 0.69/0.64    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | ~r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(subsumption_resolution,[],[f349,f81])).
% 0.69/0.64  fof(f349,plain,(
% 0.69/0.64    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(X0)) | k1_funct_1(sK1,sK3) = k1_funct_1(X0,sK3) | ~r1_partfun1(sK1,X0)) )),
% 0.69/0.64    inference(resolution,[],[f347,f27])).
% 0.69/0.64  % SZS output end Proof for theBenchmark
% 0.69/0.64  % (31163)------------------------------
% 0.69/0.64  % (31163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.69/0.64  % (31163)Termination reason: Refutation
% 0.69/0.64  
% 0.69/0.64  % (31163)Memory used [KB]: 1663
% 0.69/0.64  % (31163)Time elapsed: 0.016 s
% 0.69/0.64  % (31163)------------------------------
% 0.69/0.64  % (31163)------------------------------
% 0.69/0.64  % (31150)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.69/0.64  % (31157)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.69/0.65  % (31016)Success in time 0.283 s
%------------------------------------------------------------------------------

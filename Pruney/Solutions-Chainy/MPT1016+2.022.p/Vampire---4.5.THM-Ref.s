%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 (11659 expanded)
%              Number of leaves         :   12 (2277 expanded)
%              Depth                    :   36
%              Number of atoms          :  331 (59404 expanded)
%              Number of equality atoms :  132 (17497 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(subsumption_resolution,[],[f282,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f282,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f279,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f279,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(resolution,[],[f231,f275])).

fof(f275,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f271,f53])).

fof(f271,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f248,f268])).

fof(f268,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f267,f236])).

fof(f236,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f210,f215])).

fof(f215,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f214,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f214,plain,(
    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f213,f188])).

fof(f188,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f187,f131])).

fof(f131,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f124,f27])).

% (3218)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f27,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f124,plain,
    ( v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f123,f84])).

fof(f84,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f70,f77])).

fof(f77,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f122,f89])).

fof(f89,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f69,f77])).

fof(f69,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f103,f92])).

fof(f92,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f80,f87])).

fof(f87,plain,
    ( sK0 = k1_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f72,f73])).

fof(f73,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f71,f32])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f31,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f67,f77])).

fof(f67,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK5(sK1))
      | sK5(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK5(sK1))
      | sK5(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f90,f29])).

fof(f29,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f83,f87])).

fof(f83,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f68,f77])).

fof(f68,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f187,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f186,f132])).

fof(f132,plain,
    ( sK2 != sK3
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f124,f28])).

fof(f28,plain,
    ( ~ v2_funct_1(sK1)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f160,f134])).

fof(f134,plain,
    ( r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f124,f25])).

fof(f25,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1,sK3) != k1_funct_1(sK1,X0)
      | sK3 = X0 ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK3) != k1_funct_1(sK1,X0)
      | sK3 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f133,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f95,f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f94,f77])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f36,f87])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f133,plain,
    ( r2_hidden(sK3,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f124,f26])).

fof(f26,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f213,plain,(
    sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(subsumption_resolution,[],[f212,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f212,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(forward_demodulation,[],[f196,f58])).

fof(f196,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f78,f188])).

fof(f78,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0) ),
    inference(resolution,[],[f76,f57])).

% (3218)Refutation not found, incomplete strategy% (3218)------------------------------
% (3218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f210,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f193,f58])).

fof(f193,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f32,f188])).

fof(f267,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f266,f58])).

fof(f266,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f262,f234])).

fof(f234,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f194,f215])).

fof(f194,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f73,f188])).

fof(f262,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f233,f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f233,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f192,f215])).

fof(f192,plain,(
    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f31,f188])).

fof(f248,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f225,f215])).

fof(f225,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f82,f215])).

fof(f82,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f80,f41])).

fof(f231,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | r2_hidden(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f189,f215])).

fof(f189,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(backward_demodulation,[],[f25,f188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:13:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (3216)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (3224)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (3216)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (3234)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f282,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f279,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f231,f275])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    v2_funct_1(k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f271,f53])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | v2_funct_1(k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f248,f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f267,f236])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    inference(backward_demodulation,[],[f210,f215])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    k1_xboole_0 = sK1),
% 0.20/0.50    inference(forward_demodulation,[],[f214,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(forward_demodulation,[],[f213,f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f187,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f124,f27])).
% 0.20/0.50  % (3218)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    inference(negated_conjecture,[],[f13])).
% 0.20/0.50  fof(f13,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f123,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f70,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f32,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f30,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f122,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.50    inference(resolution,[],[f69,f77])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f30,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f103,f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f80,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    sK0 = k1_relat_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f72,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.50    inference(resolution,[],[f32,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    sK0 = k1_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f32])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.50    inference(resolution,[],[f31,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f67,f77])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f30,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | v2_funct_1(sK1) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK5(sK1)) | sK5(sK1) = X0) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK5(sK1)) | sK5(sK1) = X0 | v2_funct_1(sK1)) )),
% 0.20/0.50    inference(resolution,[],[f90,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(superposition,[],[f83,f87])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f68,f77])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f30,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f186,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    sK2 != sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f124,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | sK2 != sK3),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | sK2 = sK3),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f177])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f160,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    r2_hidden(sK2,sK0) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f124,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | r2_hidden(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK3) != k1_funct_1(sK1,X0) | sK3 = X0) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f157])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK3) != k1_funct_1(sK1,X0) | sK3 = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(resolution,[],[f133,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f29])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f77])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f93,f30])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.20/0.50    inference(superposition,[],[f36,f87])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    r2_hidden(sK3,sK0) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(resolution,[],[f124,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~v2_funct_1(sK1) | r2_hidden(sK3,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f212,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,sK1) | sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f196,f58])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.20/0.50    inference(backward_demodulation,[],[f78,f188])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | sK1 = k2_zfmisc_1(sK0,sK0)),
% 0.20/0.50    inference(resolution,[],[f76,f57])).
% 0.20/0.50  % (3218)Refutation not found, incomplete strategy% (3218)------------------------------
% 0.20/0.50  % (3218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.20/0.50    inference(resolution,[],[f32,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    inference(forward_demodulation,[],[f193,f58])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f32,f188])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(forward_demodulation,[],[f266,f58])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    inference(forward_demodulation,[],[f262,f234])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f194,f215])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f73,f188])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    inference(resolution,[],[f233,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f192,f215])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f31,f188])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | v2_funct_1(k1_xboole_0)),
% 0.20/0.50    inference(forward_demodulation,[],[f225,f215])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    v2_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f82,f215])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f80,f41])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~v2_funct_1(k1_xboole_0) | r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.50    inference(backward_demodulation,[],[f189,f215])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    r2_hidden(sK2,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f25,f188])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (3216)------------------------------
% 0.20/0.50  % (3216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3216)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (3216)Memory used [KB]: 6140
% 0.20/0.50  % (3216)Time elapsed: 0.066 s
% 0.20/0.50  % (3216)------------------------------
% 0.20/0.50  % (3216)------------------------------
% 0.20/0.50  % (3218)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3218)Memory used [KB]: 1663
% 0.20/0.50  % (3218)Time elapsed: 0.064 s
% 0.20/0.50  % (3218)------------------------------
% 0.20/0.50  % (3218)------------------------------
% 0.20/0.50  % (3210)Success in time 0.135 s
%------------------------------------------------------------------------------

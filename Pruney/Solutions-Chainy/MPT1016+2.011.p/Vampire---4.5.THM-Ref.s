%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 (2761 expanded)
%              Number of leaves         :   10 ( 534 expanded)
%              Depth                    :   31
%              Number of atoms          :  301 (13171 expanded)
%              Number of equality atoms :   88 (3110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(subsumption_resolution,[],[f308,f124])).

fof(f124,plain,(
    sK2 != sK3 ),
    inference(resolution,[],[f120,f32])).

fof(f32,plain,
    ( ~ v2_funct_1(sK1)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f120,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f119,f77])).

fof(f77,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f61,f67])).

fof(f67,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f119,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f117,f84])).

fof(f84,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f60,f67])).

fof(f60,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f117,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f95,f96])).

fof(f96,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f81,f68])).

fof(f68,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f65,f66])).

fof(f66,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X1) ) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

% (15417)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f70,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f59,f67])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f74,f68])).

fof(f74,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X1) ) ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f58,f67])).

fof(f58,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f308,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f292,f307])).

fof(f307,plain,(
    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f306,f67])).

fof(f306,plain,
    ( ~ v1_relat_1(sK1)
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f304,f34])).

fof(f304,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(resolution,[],[f241,f120])).

fof(f241,plain,(
    ! [X6] :
      ( ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | sK2 = k1_funct_1(k2_funct_1(X6),k1_funct_1(X6,sK2)) ) ),
    inference(resolution,[],[f215,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f215,plain,(
    ! [X1] : r2_hidden(sK2,X1) ),
    inference(subsumption_resolution,[],[f203,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f203,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK2,X1) ) ),
    inference(backward_demodulation,[],[f145,f170])).

fof(f170,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f169,f124])).

fof(f169,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f157,f155])).

fof(f155,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f154,f123])).

fof(f123,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f120,f31])).

fof(f31,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f153,f120])).

fof(f153,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f141,f64])).

fof(f64,plain,
    ( ~ sP6(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f62,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f37,f56_D])).

fof(f56,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f56_D])).

fof(f56_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f35,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3)) ) ),
    inference(resolution,[],[f125,f56])).

fof(f125,plain,(
    r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f120,f30])).

fof(f30,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f157,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f156,f120])).

fof(f156,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f147,f64])).

fof(f147,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2)) ) ),
    inference(resolution,[],[f126,f56])).

fof(f126,plain,(
    r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f120,f29])).

fof(f29,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f145,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK2,X1) ) ),
    inference(resolution,[],[f126,f44])).

fof(f292,plain,(
    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f291,f123])).

fof(f291,plain,(
    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f290,f67])).

fof(f290,plain,
    ( ~ v1_relat_1(sK1)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f288,f34])).

fof(f288,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) ),
    inference(resolution,[],[f226,f120])).

fof(f226,plain,(
    ! [X6] :
      ( ~ v2_funct_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | sK3 = k1_funct_1(k2_funct_1(X6),k1_funct_1(X6,sK3)) ) ),
    inference(resolution,[],[f213,f49])).

fof(f213,plain,(
    ! [X1] : r2_hidden(sK3,X1) ),
    inference(subsumption_resolution,[],[f200,f51])).

fof(f200,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r2_hidden(sK3,X1) ) ),
    inference(backward_demodulation,[],[f139,f170])).

fof(f139,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK0,k1_zfmisc_1(X1))
      | r2_hidden(sK3,X1) ) ),
    inference(resolution,[],[f125,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (15424)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (15415)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (15416)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (15412)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (15434)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (15413)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (15420)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (15430)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (15412)Refutation not found, incomplete strategy% (15412)------------------------------
% 0.20/0.51  % (15412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15426)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (15433)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (15419)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (15436)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (15425)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (15411)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (15423)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (15416)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f309,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f308,f124])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    sK2 != sK3),
% 0.20/0.52    inference(resolution,[],[f120,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | sK2 != sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    v2_funct_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f119,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f61,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f36,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f117,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.52    inference(resolution,[],[f60,f67])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f95,f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f81,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f65,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f36,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f36,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f70,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  % (15417)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f59,f67])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_funct_1(sK1) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(sK1) | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0 | v2_funct_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f89,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f74,f68])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f69,f44])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f58,f67])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f308,plain,(
% 0.20/0.52    sK2 = sK3),
% 0.20/0.52    inference(backward_demodulation,[],[f292,f307])).
% 0.20/0.52  fof(f307,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f306,f67])).
% 0.20/0.52  fof(f306,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f304,f34])).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f241,f120])).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    ( ! [X6] : (~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | sK2 = k1_funct_1(k2_funct_1(X6),k1_funct_1(X6,sK2))) )),
% 0.20/0.52    inference(resolution,[],[f215,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK2,X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f203,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK2,X1)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f145,f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f169,f124])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(superposition,[],[f157,f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(forward_demodulation,[],[f154,f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    inference(resolution,[],[f120,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f120])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f141,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~sP6(sK1,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f63,f36])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f34])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f35,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.20/0.52    inference(general_splitting,[],[f37,f56_D])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f56_D])).
% 0.20/0.52  fof(f56_D,plain,(
% 0.20/0.52    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X3] : (sP6(X3,sK0) | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3))) )),
% 0.20/0.52    inference(resolution,[],[f125,f56])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    r2_hidden(sK3,sK0)),
% 0.20/0.52    inference(resolution,[],[f120,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | r2_hidden(sK3,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f120])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f147,f64])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X3] : (sP6(X3,sK0) | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2))) )),
% 0.20/0.52    inference(resolution,[],[f126,f56])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(resolution,[],[f120,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK2,X1)) )),
% 0.20/0.52    inference(resolution,[],[f126,f44])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f291,f123])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f290,f67])).
% 0.20/0.52  fof(f290,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f288,f34])).
% 0.20/0.52  fof(f288,plain,(
% 0.20/0.52    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))),
% 0.20/0.52    inference(resolution,[],[f226,f120])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    ( ! [X6] : (~v2_funct_1(X6) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | sK3 = k1_funct_1(k2_funct_1(X6),k1_funct_1(X6,sK3))) )),
% 0.20/0.52    inference(resolution,[],[f213,f49])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK3,X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f200,f51])).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r2_hidden(sK3,X1)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f139,f170])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(sK0,k1_zfmisc_1(X1)) | r2_hidden(sK3,X1)) )),
% 0.20/0.52    inference(resolution,[],[f125,f44])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15432)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (15416)------------------------------
% 0.20/0.52  % (15416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15416)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15416)Memory used [KB]: 6268
% 0.20/0.52  % (15416)Time elapsed: 0.109 s
% 0.20/0.52  % (15416)------------------------------
% 0.20/0.52  % (15416)------------------------------
% 0.20/0.52  % (15410)Success in time 0.162 s
%------------------------------------------------------------------------------

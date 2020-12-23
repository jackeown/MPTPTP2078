%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 (44729 expanded)
%              Number of leaves         :    5 (8213 expanded)
%              Depth                    :   39
%              Number of atoms          :  350 (276901 expanded)
%              Number of equality atoms :  158 (110386 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(subsumption_resolution,[],[f236,f214])).

fof(f214,plain,(
    sK3 != sK4 ),
    inference(resolution,[],[f204,f18])).

fof(f18,plain,
    ( ~ v2_funct_1(sK2)
    | sK3 != sK4 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v2_funct_1(X2)
          <=> ! [X3,X4] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  & r2_hidden(X4,X0)
                  & r2_hidden(X3,X0) )
               => X3 = X4 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

fof(f204,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f203,f55])).

fof(f55,plain,
    ( sK5(sK2) != sK6(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( ~ v1_relat_1(sK2)
    | sK5(sK2) != sK6(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK5(X0) != sK6(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f203,plain,
    ( v2_funct_1(sK2)
    | sK5(sK2) = sK6(sK2) ),
    inference(subsumption_resolution,[],[f202,f64])).

fof(f64,plain,
    ( v2_funct_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2)) ),
    inference(resolution,[],[f44,f48])).

fof(f44,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f202,plain,
    ( v2_funct_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | sK5(sK2) = sK6(sK2) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( v2_funct_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | sK5(sK2) = sK6(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f188,f173])).

fof(f173,plain,
    ( r2_hidden(sK5(sK2),k1_xboole_0)
    | v2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f51,f171])).

fof(f171,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f165,f170])).

fof(f170,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f167,f164])).

fof(f164,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f152,f157])).

fof(f157,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f20,f150])).

fof(f150,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f149,f95])).

fof(f95,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f17])).

fof(f17,plain,
    ( ~ v2_funct_1(sK2)
    | k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,
    ( v2_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | v2_funct_1(sK2)
    | sK5(sK2) = sK6(sK2) ),
    inference(subsumption_resolution,[],[f86,f64])).

fof(f86,plain,
    ( k1_xboole_0 = sK1
    | v2_funct_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | sK5(sK2) = sK6(sK2) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | v2_funct_1(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | sK5(sK2) = sK6(sK2)
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,
    ( r2_hidden(sK5(sK2),sK0)
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f51,f56])).

fof(f56,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f47,f49])).

fof(f49,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f47,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f22,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | v2_funct_1(sK2)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))
      | sK6(sK2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( v2_funct_1(sK2)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))
      | sK6(sK2) = X0
      | v2_funct_1(sK2) ) ),
    inference(resolution,[],[f58,f19])).

fof(f19,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X3) != k1_funct_1(sK2,X4)
      | X3 = X4
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,
    ( r2_hidden(sK6(sK2),sK0)
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f53,f56])).

fof(f53,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f43,f48])).

fof(f43,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK6(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f148,f96])).

fof(f96,plain,
    ( sK3 != sK4
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f18])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4)
    | sK3 = sK4 ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,
    ( k1_xboole_0 = sK1
    | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4)
    | sK3 = sK4
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f123,f98])).

fof(f98,plain,
    ( r2_hidden(sK3,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f15])).

fof(f15,plain,
    ( ~ v2_funct_1(sK2)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,X0)
      | sK4 = X0 ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,X0)
      | sK4 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f97,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f62,f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f60,f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f24,f56])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,
    ( r2_hidden(sK4,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f88,f16])).

fof(f16,plain,
    ( ~ v2_funct_1(sK2)
    | r2_hidden(sK4,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f152,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f23,f150])).

fof(f167,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f163,f37])).

fof(f37,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f163,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f151,f157])).

fof(f151,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f22,f150])).

fof(f165,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f153,f157])).

fof(f153,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f49,f150])).

fof(f51,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f188,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | v2_funct_1(sK2)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))
      | sK6(sK2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( v2_funct_1(sK2)
      | ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))
      | sK6(sK2) = X0
      | v2_funct_1(sK2) ) ),
    inference(resolution,[],[f172,f166])).

fof(f166,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ r2_hidden(X3,k1_xboole_0)
      | k1_funct_1(sK2,X3) != k1_funct_1(sK2,X4)
      | X3 = X4
      | v2_funct_1(sK2) ) ),
    inference(forward_demodulation,[],[f160,f157])).

fof(f160,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X3) != k1_funct_1(sK2,X4)
      | X3 = X4
      | v2_funct_1(sK2) ) ),
    inference(backward_demodulation,[],[f19,f157])).

fof(f172,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | v2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f53,f171])).

fof(f236,plain,(
    sK3 = sK4 ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | sK3 = sK4 ),
    inference(resolution,[],[f228,f212])).

fof(f212,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(resolution,[],[f204,f158])).

fof(f158,plain,
    ( ~ v2_funct_1(sK2)
    | r2_hidden(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f15,f157])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
      | sK4 = X0 ) ),
    inference(forward_demodulation,[],[f226,f213])).

fof(f213,plain,(
    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f204,f17])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK2,sK4) != k1_funct_1(sK2,X0)
      | sK4 = X0 ) ),
    inference(resolution,[],[f211,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f179,f166])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f178,f48])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f177,f21])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
      | X0 = X1
      | ~ v2_funct_1(sK2) ) ),
    inference(superposition,[],[f24,f171])).

fof(f211,plain,(
    r2_hidden(sK4,k1_xboole_0) ),
    inference(resolution,[],[f204,f159])).

fof(f159,plain,
    ( ~ v2_funct_1(sK2)
    | r2_hidden(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f16,f157])).

%------------------------------------------------------------------------------

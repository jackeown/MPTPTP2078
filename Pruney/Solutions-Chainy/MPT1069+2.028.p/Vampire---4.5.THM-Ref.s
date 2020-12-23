%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:46 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  167 (8453 expanded)
%              Number of leaves         :   18 (1605 expanded)
%              Depth                    :   47
%              Number of atoms          :  517 (51087 expanded)
%              Number of equality atoms :  130 (11281 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f575,plain,(
    $false ),
    inference(resolution,[],[f574,f441])).

fof(f441,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f440,f428])).

fof(f428,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f388,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f388,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f387,f356])).

fof(f356,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f280,f255])).

fof(f255,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f50,f252])).

fof(f252,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f245,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f245,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f221,f52])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = sK2
      | sK1 = X0 ) ),
    inference(resolution,[],[f219,f62])).

fof(f62,plain,(
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

fof(f219,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f215,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f215,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f213,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f213,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f208,f95])).

fof(f95,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f42,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f208,plain,
    ( ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f206,f164])).

fof(f164,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f163,f105])).

fof(f105,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f163,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f49,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f206,plain,(
    ~ r2_hidden(sK5,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f205,f107])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f205,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f204,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f204,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f202,f137])).

fof(f137,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f122,f106])).

fof(f106,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f43,f97])).

fof(f97,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f47,f71])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f202,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f200,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f200,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5),X0)
      | ~ r1_tarski(X0,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f199,f47])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r2_hidden(k1_funct_1(sK3,sK5),X1)
      | ~ r1_tarski(X1,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f198,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(resolution,[],[f197,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f197,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK0) ),
    inference(superposition,[],[f194,f172])).

fof(f172,plain,(
    ! [X6,X7] :
      ( k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7)
      | ~ r2_hidden(X7,k1_relat_1(sK4))
      | ~ v5_relat_1(sK4,X6) ) ),
    inference(subsumption_resolution,[],[f91,f99])).

fof(f99,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f47,f69])).

fof(f91,plain,(
    ! [X6,X7] :
      ( ~ v5_relat_1(sK4,X6)
      | ~ v1_relat_1(sK4)
      | ~ r2_hidden(X7,k1_relat_1(sK4))
      | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7) ) ),
    inference(resolution,[],[f46,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f194,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f45,f193])).

fof(f193,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f118,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f116,f46])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      | ~ m1_subset_1(X0,sK1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    inference(resolution,[],[f43,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f45,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f280,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f278,f44])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(resolution,[],[f254,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f254,plain,(
    v1_funct_2(sK3,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f252])).

fof(f387,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(sK3) = X0 ) ),
    inference(subsumption_resolution,[],[f386,f52])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
      | ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(sK3) = X0 ) ),
    inference(forward_demodulation,[],[f364,f356])).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
      | k1_relat_1(sK3) = X0 ) ),
    inference(backward_demodulation,[],[f161,f356])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X0,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK3))
      | k1_relat_1(sK3) = X0 ) ),
    inference(resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(sK3) = X1
      | ~ r1_tarski(X1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f146,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK3,X0)
      | ~ r1_tarski(X0,k1_relat_1(sK3))
      | k1_relat_1(sK3) = X0 ) ),
    inference(resolution,[],[f111,f62])).

fof(f111,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(sK3),X1)
      | ~ v4_relat_1(sK3,X1) ) ),
    inference(resolution,[],[f107,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f440,plain,(
    ~ r1_tarski(sK1,k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f437,f44])).

fof(f437,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f385,f428])).

fof(f385,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k1_xboole_0))
    | sK1 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f363,f356])).

fof(f363,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f160,f356])).

fof(f160,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f153,f50])).

fof(f574,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(condensation,[],[f573])).

fof(f573,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK1,X5)
      | r1_tarski(sK1,X6) ) ),
    inference(resolution,[],[f569,f64])).

fof(f569,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | r1_tarski(sK1,X5) ) ),
    inference(subsumption_resolution,[],[f564,f516])).

fof(f516,plain,(
    ~ r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f515])).

fof(f515,plain,
    ( k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5)) != k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5))
    | ~ r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0) ),
    inference(superposition,[],[f366,f513])).

fof(f513,plain,(
    ! [X0] :
      ( k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f484,f253])).

fof(f253,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(backward_demodulation,[],[f47,f252])).

fof(f484,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,k1_xboole_0)
      | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1) ) ),
    inference(resolution,[],[f291,f73])).

fof(f291,plain,(
    ! [X6,X7] :
      ( ~ v5_relat_1(sK4,X6)
      | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7)
      | ~ r2_hidden(X7,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f172,f277])).

fof(f277,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f276,f52])).

fof(f276,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK4))
    | k1_xboole_0 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f269,f252])).

fof(f269,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ r1_tarski(sK2,k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f157,f252])).

fof(f157,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK4))
    | sK2 = k1_relat_1(sK4) ),
    inference(resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(sK4) = X1
      | ~ r1_tarski(X1,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f145,f72])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK4,X0)
      | ~ r1_tarski(X0,k1_relat_1(sK4))
      | k1_relat_1(sK4) = X0 ) ),
    inference(resolution,[],[f103,f62])).

fof(f103,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(sK4),X1)
      | ~ v4_relat_1(sK4,X1) ) ),
    inference(resolution,[],[f99,f56])).

fof(f366,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(k1_xboole_0,sK5)) != k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5)) ),
    inference(backward_demodulation,[],[f194,f356])).

fof(f564,plain,(
    ! [X4,X5] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0)
      | ~ r2_hidden(X4,sK1)
      | r1_tarski(sK1,X5) ) ),
    inference(superposition,[],[f539,f560])).

fof(f560,plain,(
    ! [X2] :
      ( k1_funct_1(k1_xboole_0,sK5) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f556,f64])).

fof(f556,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(k1_xboole_0,sK5) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5) ) ),
    inference(resolution,[],[f555,f42])).

fof(f555,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f554,f54])).

fof(f554,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f553,f372])).

fof(f372,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f255,f356])).

fof(f553,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
      | ~ m1_subset_1(X0,sK1)
      | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f391,f371])).

fof(f371,plain,(
    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f254,f356])).

fof(f391,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,k1_xboole_0,X2) = k1_funct_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f357,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f357,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f48,f356])).

fof(f539,plain,(
    ! [X1] :
      ( r2_hidden(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f538,f256])).

fof(f256,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f252])).

fof(f538,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | v1_xboole_0(k1_xboole_0)
      | r2_hidden(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) ) ),
    inference(resolution,[],[f536,f57])).

fof(f536,plain,(
    ! [X0] :
      ( m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f535,f42])).

fof(f535,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f534,f54])).

fof(f534,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X0,sK1)
      | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f533,f372])).

fof(f533,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
      | ~ m1_subset_1(X0,sK1)
      | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f392,f371])).

fof(f392,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(k1_xboole_0,X3,X4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,X3)
      | m1_subset_1(k3_funct_2(X3,X4,k1_xboole_0,X5),X4) ) ),
    inference(resolution,[],[f357,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15985)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (15969)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (15959)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15962)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15977)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (15965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15958)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (15979)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (15973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15971)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15980)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.53  % (15972)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (15961)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (15960)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.54  % (15963)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (15987)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (15967)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (15964)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.54  % (15970)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (15966)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.54  % (15968)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (15978)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (15968)Refutation not found, incomplete strategy% (15968)------------------------------
% 1.35/0.55  % (15968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (15968)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (15968)Memory used [KB]: 10874
% 1.35/0.55  % (15968)Time elapsed: 0.126 s
% 1.35/0.55  % (15968)------------------------------
% 1.35/0.55  % (15968)------------------------------
% 1.35/0.55  % (15966)Refutation not found, incomplete strategy% (15966)------------------------------
% 1.35/0.55  % (15966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (15984)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (15983)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.55  % (15976)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.55  % (15982)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.56  % (15986)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.56  % (15975)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.56  % (15974)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.56  % (15981)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (15966)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (15966)Memory used [KB]: 11001
% 1.49/0.57  % (15966)Time elapsed: 0.130 s
% 1.49/0.57  % (15966)------------------------------
% 1.49/0.57  % (15966)------------------------------
% 1.49/0.58  % (15979)Refutation found. Thanks to Tanya!
% 1.49/0.58  % SZS status Theorem for theBenchmark
% 1.49/0.58  % SZS output start Proof for theBenchmark
% 1.49/0.58  fof(f575,plain,(
% 1.49/0.58    $false),
% 1.49/0.58    inference(resolution,[],[f574,f441])).
% 1.49/0.58  fof(f441,plain,(
% 1.49/0.58    ~r1_tarski(sK1,k1_xboole_0)),
% 1.49/0.58    inference(forward_demodulation,[],[f440,f428])).
% 1.49/0.58  fof(f428,plain,(
% 1.49/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(resolution,[],[f388,f52])).
% 1.49/0.58  fof(f52,plain,(
% 1.49/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f4])).
% 1.49/0.58  fof(f4,axiom,(
% 1.49/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.58  fof(f388,plain,(
% 1.49/0.58    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0) )),
% 1.49/0.58    inference(forward_demodulation,[],[f387,f356])).
% 1.49/0.58  fof(f356,plain,(
% 1.49/0.58    k1_xboole_0 = sK3),
% 1.49/0.58    inference(subsumption_resolution,[],[f280,f255])).
% 1.49/0.58  fof(f255,plain,(
% 1.49/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.49/0.58    inference(backward_demodulation,[],[f50,f252])).
% 1.49/0.58  fof(f252,plain,(
% 1.49/0.58    k1_xboole_0 = sK2),
% 1.49/0.58    inference(subsumption_resolution,[],[f245,f44])).
% 1.49/0.58  fof(f44,plain,(
% 1.49/0.58    k1_xboole_0 != sK1),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f21,plain,(
% 1.49/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.49/0.58    inference(flattening,[],[f20])).
% 1.49/0.58  fof(f20,plain,(
% 1.49/0.58    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.49/0.58    inference(ennf_transformation,[],[f19])).
% 1.49/0.58  fof(f19,negated_conjecture,(
% 1.49/0.58    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.49/0.58    inference(negated_conjecture,[],[f18])).
% 1.49/0.58  fof(f18,conjecture,(
% 1.49/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.49/0.58  fof(f245,plain,(
% 1.49/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.49/0.58    inference(resolution,[],[f221,f52])).
% 1.49/0.58  fof(f221,plain,(
% 1.49/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = sK2 | sK1 = X0) )),
% 1.49/0.58    inference(resolution,[],[f219,f62])).
% 1.49/0.58  fof(f62,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f3])).
% 1.49/0.58  fof(f3,axiom,(
% 1.49/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.58  fof(f219,plain,(
% 1.49/0.58    ( ! [X2] : (r1_tarski(sK1,X2) | k1_xboole_0 = sK2) )),
% 1.49/0.58    inference(resolution,[],[f215,f64])).
% 1.49/0.58  fof(f64,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f29])).
% 1.49/0.58  fof(f29,plain,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f2])).
% 1.49/0.58  fof(f2,axiom,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.58  fof(f215,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK2) )),
% 1.49/0.58    inference(resolution,[],[f213,f54])).
% 1.49/0.58  fof(f54,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f1])).
% 1.49/0.58  fof(f1,axiom,(
% 1.49/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.58  fof(f213,plain,(
% 1.49/0.58    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 1.49/0.58    inference(resolution,[],[f208,f95])).
% 1.49/0.58  fof(f95,plain,(
% 1.49/0.58    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 1.49/0.58    inference(resolution,[],[f42,f57])).
% 1.49/0.58  fof(f57,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f24])).
% 1.49/0.58  fof(f24,plain,(
% 1.49/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.49/0.58    inference(flattening,[],[f23])).
% 1.49/0.58  fof(f23,plain,(
% 1.49/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f5])).
% 1.49/0.58  fof(f5,axiom,(
% 1.49/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.49/0.58  fof(f42,plain,(
% 1.49/0.58    m1_subset_1(sK5,sK1)),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f208,plain,(
% 1.49/0.58    ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2),
% 1.49/0.58    inference(superposition,[],[f206,f164])).
% 1.49/0.58  fof(f164,plain,(
% 1.49/0.58    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 1.49/0.58    inference(superposition,[],[f163,f105])).
% 1.49/0.58  fof(f105,plain,(
% 1.49/0.58    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 1.49/0.58    inference(resolution,[],[f50,f71])).
% 1.49/0.58  fof(f71,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f34])).
% 1.49/0.58  fof(f34,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(ennf_transformation,[],[f11])).
% 1.49/0.58  fof(f11,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.58  fof(f163,plain,(
% 1.49/0.58    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2),
% 1.49/0.58    inference(subsumption_resolution,[],[f96,f50])).
% 1.49/0.58  fof(f96,plain,(
% 1.49/0.58    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.58    inference(resolution,[],[f49,f79])).
% 1.49/0.58  fof(f79,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f37])).
% 1.49/0.58  fof(f37,plain,(
% 1.49/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(flattening,[],[f36])).
% 1.49/0.58  fof(f36,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(ennf_transformation,[],[f13])).
% 1.49/0.58  fof(f13,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.49/0.58  fof(f49,plain,(
% 1.49/0.58    v1_funct_2(sK3,sK1,sK2)),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f206,plain,(
% 1.49/0.58    ~r2_hidden(sK5,k1_relat_1(sK3))),
% 1.49/0.58    inference(subsumption_resolution,[],[f205,f107])).
% 1.49/0.58  fof(f107,plain,(
% 1.49/0.58    v1_relat_1(sK3)),
% 1.49/0.58    inference(resolution,[],[f50,f69])).
% 1.49/0.58  fof(f69,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f32])).
% 1.49/0.58  fof(f32,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(ennf_transformation,[],[f9])).
% 1.49/0.58  fof(f9,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.58  fof(f205,plain,(
% 1.49/0.58    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.49/0.58    inference(subsumption_resolution,[],[f204,f48])).
% 1.49/0.58  fof(f48,plain,(
% 1.49/0.58    v1_funct_1(sK3)),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f204,plain,(
% 1.49/0.58    ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.49/0.58    inference(subsumption_resolution,[],[f202,f137])).
% 1.49/0.58  fof(f137,plain,(
% 1.49/0.58    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 1.49/0.58    inference(backward_demodulation,[],[f122,f106])).
% 1.49/0.58  fof(f106,plain,(
% 1.49/0.58    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.49/0.58    inference(resolution,[],[f50,f70])).
% 1.49/0.58  fof(f70,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f33])).
% 1.49/0.58  fof(f33,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(ennf_transformation,[],[f12])).
% 1.49/0.58  fof(f12,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.49/0.58  fof(f122,plain,(
% 1.49/0.58    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 1.49/0.58    inference(backward_demodulation,[],[f43,f97])).
% 1.49/0.58  fof(f97,plain,(
% 1.49/0.58    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 1.49/0.58    inference(resolution,[],[f47,f71])).
% 1.49/0.58  fof(f47,plain,(
% 1.49/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f43,plain,(
% 1.49/0.58    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f202,plain,(
% 1.49/0.58    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.49/0.58    inference(resolution,[],[f200,f58])).
% 1.49/0.58  fof(f58,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f26])).
% 1.49/0.58  fof(f26,plain,(
% 1.49/0.58    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.49/0.58    inference(flattening,[],[f25])).
% 1.49/0.58  fof(f25,plain,(
% 1.49/0.58    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.49/0.58    inference(ennf_transformation,[],[f8])).
% 1.49/0.58  fof(f8,axiom,(
% 1.49/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.49/0.58  fof(f200,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),X0) | ~r1_tarski(X0,k1_relat_1(sK4))) )),
% 1.49/0.58    inference(resolution,[],[f199,f47])).
% 1.49/0.58  fof(f199,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r2_hidden(k1_funct_1(sK3,sK5),X1) | ~r1_tarski(X1,k1_relat_1(sK4))) )),
% 1.49/0.58    inference(resolution,[],[f198,f63])).
% 1.49/0.58  fof(f63,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f29])).
% 1.49/0.58  fof(f198,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 1.49/0.58    inference(resolution,[],[f197,f73])).
% 1.49/0.58  fof(f73,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f35])).
% 1.49/0.58  fof(f35,plain,(
% 1.49/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.58    inference(ennf_transformation,[],[f10])).
% 1.49/0.58  fof(f10,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.58  fof(f197,plain,(
% 1.49/0.58    ~v5_relat_1(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 1.49/0.58    inference(trivial_inequality_removal,[],[f196])).
% 1.49/0.58  fof(f196,plain,(
% 1.49/0.58    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0)),
% 1.49/0.58    inference(superposition,[],[f194,f172])).
% 1.49/0.58  fof(f172,plain,(
% 1.49/0.58    ( ! [X6,X7] : (k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7) | ~r2_hidden(X7,k1_relat_1(sK4)) | ~v5_relat_1(sK4,X6)) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f91,f99])).
% 1.49/0.58  fof(f99,plain,(
% 1.49/0.58    v1_relat_1(sK4)),
% 1.49/0.58    inference(resolution,[],[f47,f69])).
% 1.49/0.58  fof(f91,plain,(
% 1.49/0.58    ( ! [X6,X7] : (~v5_relat_1(sK4,X6) | ~v1_relat_1(sK4) | ~r2_hidden(X7,k1_relat_1(sK4)) | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7)) )),
% 1.49/0.58    inference(resolution,[],[f46,f59])).
% 1.49/0.58  fof(f59,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f28])).
% 1.49/0.58  fof(f28,plain,(
% 1.49/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.49/0.58    inference(flattening,[],[f27])).
% 1.49/0.58  fof(f27,plain,(
% 1.49/0.58    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.49/0.58    inference(ennf_transformation,[],[f14])).
% 1.49/0.58  fof(f14,axiom,(
% 1.49/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.49/0.58  fof(f46,plain,(
% 1.49/0.58    v1_funct_1(sK4)),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f194,plain,(
% 1.49/0.58    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.49/0.58    inference(backward_demodulation,[],[f45,f193])).
% 1.49/0.58  fof(f193,plain,(
% 1.49/0.58    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.49/0.58    inference(resolution,[],[f120,f42])).
% 1.49/0.58  fof(f120,plain,(
% 1.49/0.58    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f119,f44])).
% 1.49/0.58  fof(f119,plain,(
% 1.49/0.58    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f118,f51])).
% 1.49/0.58  fof(f51,plain,(
% 1.49/0.58    ~v1_xboole_0(sK2)),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f118,plain,(
% 1.49/0.58    ( ! [X0] : (~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f117,f47])).
% 1.49/0.58  fof(f117,plain,(
% 1.49/0.58    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f116,f46])).
% 1.49/0.58  fof(f116,plain,(
% 1.49/0.58    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f115,f50])).
% 1.49/0.58  fof(f115,plain,(
% 1.49/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f114,f49])).
% 1.49/0.58  fof(f114,plain,(
% 1.49/0.58    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f112,f48])).
% 1.49/0.58  fof(f112,plain,(
% 1.49/0.58    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) )),
% 1.49/0.58    inference(resolution,[],[f43,f68])).
% 1.49/0.58  fof(f68,plain,(
% 1.49/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f31])).
% 1.49/0.58  fof(f31,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.49/0.58    inference(flattening,[],[f30])).
% 1.49/0.58  fof(f30,plain,(
% 1.49/0.58    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.49/0.58    inference(ennf_transformation,[],[f17])).
% 1.49/0.58  fof(f17,axiom,(
% 1.49/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.49/0.58  fof(f45,plain,(
% 1.49/0.58    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f50,plain,(
% 1.49/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.49/0.58    inference(cnf_transformation,[],[f21])).
% 1.49/0.58  fof(f280,plain,(
% 1.49/0.58    k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.49/0.58    inference(subsumption_resolution,[],[f278,f44])).
% 1.49/0.58  fof(f278,plain,(
% 1.49/0.58    k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.49/0.58    inference(resolution,[],[f254,f86])).
% 1.49/0.58  fof(f86,plain,(
% 1.49/0.58    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 1.49/0.58    inference(equality_resolution,[],[f75])).
% 1.49/0.58  fof(f75,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f37])).
% 1.49/0.58  fof(f254,plain,(
% 1.49/0.58    v1_funct_2(sK3,sK1,k1_xboole_0)),
% 1.49/0.58    inference(backward_demodulation,[],[f49,f252])).
% 1.49/0.58  fof(f387,plain,(
% 1.49/0.58    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(sK3) = X0) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f386,f52])).
% 1.49/0.58  fof(f386,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) | ~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(sK3) = X0) )),
% 1.49/0.58    inference(forward_demodulation,[],[f364,f356])).
% 1.49/0.58  fof(f364,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | ~r1_tarski(sK3,k2_zfmisc_1(X0,X1)) | k1_relat_1(sK3) = X0) )),
% 1.49/0.58    inference(backward_demodulation,[],[f161,f356])).
% 1.49/0.58  fof(f161,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(sK3,k2_zfmisc_1(X0,X1)) | ~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(sK3) = X0) )),
% 1.49/0.58    inference(resolution,[],[f153,f66])).
% 1.49/0.58  fof(f66,plain,(
% 1.49/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f6])).
% 1.49/0.58  fof(f6,axiom,(
% 1.49/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.58  fof(f153,plain,(
% 1.49/0.58    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(sK3) = X1 | ~r1_tarski(X1,k1_relat_1(sK3))) )),
% 1.49/0.58    inference(resolution,[],[f146,f72])).
% 1.49/0.58  fof(f72,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f35])).
% 1.49/0.58  fof(f146,plain,(
% 1.49/0.58    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(sK3) = X0) )),
% 1.49/0.58    inference(resolution,[],[f111,f62])).
% 1.49/0.58  fof(f111,plain,(
% 1.49/0.58    ( ! [X1] : (r1_tarski(k1_relat_1(sK3),X1) | ~v4_relat_1(sK3,X1)) )),
% 1.49/0.58    inference(resolution,[],[f107,f56])).
% 1.49/0.58  fof(f56,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f22])).
% 1.49/0.58  fof(f22,plain,(
% 1.49/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f7])).
% 1.49/0.58  fof(f7,axiom,(
% 1.49/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.49/0.58  fof(f440,plain,(
% 1.49/0.58    ~r1_tarski(sK1,k1_relat_1(k1_xboole_0))),
% 1.49/0.58    inference(subsumption_resolution,[],[f437,f44])).
% 1.49/0.58  fof(f437,plain,(
% 1.49/0.58    k1_xboole_0 = sK1 | ~r1_tarski(sK1,k1_relat_1(k1_xboole_0))),
% 1.49/0.58    inference(backward_demodulation,[],[f385,f428])).
% 1.49/0.58  fof(f385,plain,(
% 1.49/0.58    ~r1_tarski(sK1,k1_relat_1(k1_xboole_0)) | sK1 = k1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(forward_demodulation,[],[f363,f356])).
% 1.49/0.58  fof(f363,plain,(
% 1.49/0.58    sK1 = k1_relat_1(k1_xboole_0) | ~r1_tarski(sK1,k1_relat_1(sK3))),
% 1.49/0.58    inference(backward_demodulation,[],[f160,f356])).
% 1.49/0.58  fof(f160,plain,(
% 1.49/0.58    ~r1_tarski(sK1,k1_relat_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 1.49/0.58    inference(resolution,[],[f153,f50])).
% 1.49/0.58  fof(f574,plain,(
% 1.49/0.58    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 1.49/0.58    inference(condensation,[],[f573])).
% 1.49/0.58  fof(f573,plain,(
% 1.49/0.58    ( ! [X6,X5] : (r1_tarski(sK1,X5) | r1_tarski(sK1,X6)) )),
% 1.49/0.58    inference(resolution,[],[f569,f64])).
% 1.49/0.58  fof(f569,plain,(
% 1.49/0.58    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | r1_tarski(sK1,X5)) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f564,f516])).
% 1.49/0.58  fof(f516,plain,(
% 1.49/0.58    ~r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0)),
% 1.49/0.58    inference(trivial_inequality_removal,[],[f515])).
% 1.49/0.58  fof(f515,plain,(
% 1.49/0.58    k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5)) != k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5)) | ~r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0)),
% 1.49/0.58    inference(superposition,[],[f366,f513])).
% 1.49/0.58  fof(f513,plain,(
% 1.49/0.58    ( ! [X0] : (k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.49/0.58    inference(resolution,[],[f484,f253])).
% 1.49/0.58  fof(f253,plain,(
% 1.49/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 1.49/0.58    inference(backward_demodulation,[],[f47,f252])).
% 1.49/0.58  fof(f484,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,k1_xboole_0) | k7_partfun1(X0,sK4,X1) = k1_funct_1(sK4,X1)) )),
% 1.49/0.58    inference(resolution,[],[f291,f73])).
% 1.49/0.58  fof(f291,plain,(
% 1.49/0.58    ( ! [X6,X7] : (~v5_relat_1(sK4,X6) | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7) | ~r2_hidden(X7,k1_xboole_0)) )),
% 1.49/0.58    inference(backward_demodulation,[],[f172,f277])).
% 1.49/0.58  fof(f277,plain,(
% 1.49/0.58    k1_xboole_0 = k1_relat_1(sK4)),
% 1.49/0.58    inference(subsumption_resolution,[],[f276,f52])).
% 1.49/0.58  fof(f276,plain,(
% 1.49/0.58    ~r1_tarski(k1_xboole_0,k1_relat_1(sK4)) | k1_xboole_0 = k1_relat_1(sK4)),
% 1.49/0.58    inference(forward_demodulation,[],[f269,f252])).
% 1.49/0.58  fof(f269,plain,(
% 1.49/0.58    k1_xboole_0 = k1_relat_1(sK4) | ~r1_tarski(sK2,k1_relat_1(sK4))),
% 1.49/0.58    inference(backward_demodulation,[],[f157,f252])).
% 1.49/0.58  fof(f157,plain,(
% 1.49/0.58    ~r1_tarski(sK2,k1_relat_1(sK4)) | sK2 = k1_relat_1(sK4)),
% 1.49/0.58    inference(resolution,[],[f151,f47])).
% 1.49/0.58  fof(f151,plain,(
% 1.49/0.58    ( ! [X2,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(sK4) = X1 | ~r1_tarski(X1,k1_relat_1(sK4))) )),
% 1.49/0.58    inference(resolution,[],[f145,f72])).
% 1.49/0.58  fof(f145,plain,(
% 1.49/0.58    ( ! [X0] : (~v4_relat_1(sK4,X0) | ~r1_tarski(X0,k1_relat_1(sK4)) | k1_relat_1(sK4) = X0) )),
% 1.49/0.58    inference(resolution,[],[f103,f62])).
% 1.49/0.58  fof(f103,plain,(
% 1.49/0.58    ( ! [X1] : (r1_tarski(k1_relat_1(sK4),X1) | ~v4_relat_1(sK4,X1)) )),
% 1.49/0.58    inference(resolution,[],[f99,f56])).
% 1.49/0.58  fof(f366,plain,(
% 1.49/0.58    k7_partfun1(sK0,sK4,k1_funct_1(k1_xboole_0,sK5)) != k1_funct_1(sK4,k1_funct_1(k1_xboole_0,sK5))),
% 1.49/0.58    inference(backward_demodulation,[],[f194,f356])).
% 1.49/0.58  fof(f564,plain,(
% 1.49/0.58    ( ! [X4,X5] : (r2_hidden(k1_funct_1(k1_xboole_0,sK5),k1_xboole_0) | ~r2_hidden(X4,sK1) | r1_tarski(sK1,X5)) )),
% 1.49/0.58    inference(superposition,[],[f539,f560])).
% 1.49/0.58  fof(f560,plain,(
% 1.49/0.58    ( ! [X2] : (k1_funct_1(k1_xboole_0,sK5) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5) | r1_tarski(sK1,X2)) )),
% 1.49/0.58    inference(resolution,[],[f556,f64])).
% 1.49/0.58  fof(f556,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(k1_xboole_0,sK5) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5)) )),
% 1.49/0.58    inference(resolution,[],[f555,f42])).
% 1.49/0.58  fof(f555,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0) | ~r2_hidden(X1,sK1)) )),
% 1.49/0.58    inference(resolution,[],[f554,f54])).
% 1.49/0.58  fof(f554,plain,(
% 1.49/0.58    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0)) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f553,f372])).
% 1.49/0.58  fof(f372,plain,(
% 1.49/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.49/0.58    inference(backward_demodulation,[],[f255,f356])).
% 1.49/0.58  fof(f553,plain,(
% 1.49/0.58    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~m1_subset_1(X0,sK1) | k1_funct_1(k1_xboole_0,X0) = k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0)) )),
% 1.49/0.58    inference(resolution,[],[f391,f371])).
% 1.49/0.58  fof(f371,plain,(
% 1.49/0.58    v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 1.49/0.58    inference(backward_demodulation,[],[f254,f356])).
% 1.49/0.58  fof(f391,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(k1_xboole_0,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,k1_xboole_0,X2) = k1_funct_1(k1_xboole_0,X2)) )),
% 1.49/0.58    inference(resolution,[],[f357,f81])).
% 1.49/0.58  fof(f81,plain,(
% 1.49/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f41])).
% 1.49/0.58  fof(f41,plain,(
% 1.49/0.58    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.49/0.58    inference(flattening,[],[f40])).
% 1.49/0.58  fof(f40,plain,(
% 1.49/0.58    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f16])).
% 1.49/0.58  fof(f16,axiom,(
% 1.49/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.49/0.58  fof(f357,plain,(
% 1.49/0.58    v1_funct_1(k1_xboole_0)),
% 1.49/0.58    inference(backward_demodulation,[],[f48,f356])).
% 1.49/0.58  fof(f539,plain,(
% 1.49/0.58    ( ! [X1] : (r2_hidden(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) | ~r2_hidden(X1,sK1)) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f538,f256])).
% 1.49/0.58  fof(f256,plain,(
% 1.49/0.58    ~v1_xboole_0(k1_xboole_0)),
% 1.49/0.58    inference(backward_demodulation,[],[f51,f252])).
% 1.49/0.58  fof(f538,plain,(
% 1.49/0.58    ( ! [X1] : (~r2_hidden(X1,sK1) | v1_xboole_0(k1_xboole_0) | r2_hidden(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0)) )),
% 1.49/0.58    inference(resolution,[],[f536,f57])).
% 1.49/0.58  fof(f536,plain,(
% 1.49/0.58    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,sK5),k1_xboole_0) | ~r2_hidden(X0,sK1)) )),
% 1.49/0.58    inference(resolution,[],[f535,f42])).
% 1.49/0.58  fof(f535,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X1,sK1)) )),
% 1.49/0.58    inference(resolution,[],[f534,f54])).
% 1.49/0.58  fof(f534,plain,(
% 1.49/0.58    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f533,f372])).
% 1.49/0.58  fof(f533,plain,(
% 1.49/0.58    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)) )),
% 1.49/0.58    inference(resolution,[],[f392,f371])).
% 1.49/0.58  fof(f392,plain,(
% 1.49/0.58    ( ! [X4,X5,X3] : (~v1_funct_2(k1_xboole_0,X3,X4) | v1_xboole_0(X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,X3) | m1_subset_1(k3_funct_2(X3,X4,k1_xboole_0,X5),X4)) )),
% 1.49/0.58    inference(resolution,[],[f357,f80])).
% 1.49/0.58  fof(f80,plain,(
% 1.49/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f39])).
% 1.49/0.58  fof(f39,plain,(
% 1.49/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.49/0.58    inference(flattening,[],[f38])).
% 1.49/0.58  fof(f38,plain,(
% 1.49/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f15])).
% 1.49/0.58  fof(f15,axiom,(
% 1.49/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 1.49/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 1.49/0.58  % SZS output end Proof for theBenchmark
% 1.49/0.58  % (15979)------------------------------
% 1.49/0.58  % (15979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (15979)Termination reason: Refutation
% 1.49/0.58  
% 1.49/0.58  % (15979)Memory used [KB]: 1918
% 1.49/0.58  % (15979)Time elapsed: 0.155 s
% 1.49/0.58  % (15979)------------------------------
% 1.49/0.58  % (15979)------------------------------
% 1.49/0.58  % (15957)Success in time 0.218 s
%------------------------------------------------------------------------------

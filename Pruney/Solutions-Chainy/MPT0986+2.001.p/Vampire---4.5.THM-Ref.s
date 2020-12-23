%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 140 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 ( 657 expanded)
%              Number of equality atoms :   73 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f337,plain,(
    $false ),
    inference(subsumption_resolution,[],[f336,f46])).

fof(f46,plain,(
    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f336,plain,(
    sK2 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) ),
    inference(resolution,[],[f333,f44])).

fof(f44,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f333,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f332,f266])).

fof(f266,plain,(
    sK0 = k2_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f116,f263])).

fof(f263,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f119,f262])).

fof(f262,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f261,f41])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f261,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f260,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f73,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f119,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f116,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f115,f81])).

fof(f81,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f115,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f332,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK3))) ) ),
    inference(forward_demodulation,[],[f331,f98])).

fof(f98,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f97,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f331,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK3))) ) ),
    inference(subsumption_resolution,[],[f330,f81])).

fof(f330,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK3)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f328,f40])).

fof(f328,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK3)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f219,f43])).

fof(f219,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f218,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f218,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | ~ r2_hidden(X2,k2_relat_1(k2_funct_1(X1)))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f215,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f215,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ r2_hidden(X2,k2_relat_1(k2_funct_1(X1)))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (25577)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.48  % (25580)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.49  % (25577)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f337,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f336,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    sK2 != k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f15])).
% 0.22/0.49  fof(f15,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.49  fof(f336,plain,(
% 0.22/0.49    sK2 = k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2))),
% 0.22/0.49    inference(resolution,[],[f333,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    r2_hidden(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f333,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f332,f266])).
% 0.22/0.49  fof(f266,plain,(
% 0.22/0.49    sK0 = k2_relat_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(backward_demodulation,[],[f116,f263])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3)),
% 0.22/0.49    inference(backward_demodulation,[],[f119,f262])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f261,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f260,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f73,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    inference(resolution,[],[f65,f42])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f64,f42])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(subsumption_resolution,[],[f113,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(resolution,[],[f55,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v2_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.49  fof(f332,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(k2_funct_1(sK3)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f331,f98])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(subsumption_resolution,[],[f97,f81])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(subsumption_resolution,[],[f95,f40])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 0.22/0.49    inference(resolution,[],[f53,f43])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.49  fof(f331,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(k2_funct_1(sK3)))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f330,f81])).
% 0.22/0.49  fof(f330,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f328,f40])).
% 0.22/0.49  fof(f328,plain,(
% 0.22/0.49    ( ! [X0] : (k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),X0)) = X0 | ~v1_funct_1(sK3) | ~r2_hidden(X0,k2_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(sK3)) )),
% 0.22/0.49    inference(resolution,[],[f219,f43])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v2_funct_1(X1) | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2 | ~v1_funct_1(X1) | ~r2_hidden(X2,k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f218,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v1_relat_1(k2_funct_1(X1)) | ~r2_hidden(X2,k2_relat_1(k2_funct_1(X1))) | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2 | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f215,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~r2_hidden(X2,k2_relat_1(k2_funct_1(X1))) | k1_funct_1(k2_funct_1(X1),k1_funct_1(k2_funct_1(k2_funct_1(X1)),X2)) = X2 | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(resolution,[],[f58,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (25577)------------------------------
% 0.22/0.49  % (25577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25577)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (25577)Memory used [KB]: 1791
% 0.22/0.49  % (25577)Time elapsed: 0.018 s
% 0.22/0.49  % (25577)------------------------------
% 0.22/0.49  % (25577)------------------------------
% 0.22/0.50  % (25557)Success in time 0.128 s
%------------------------------------------------------------------------------

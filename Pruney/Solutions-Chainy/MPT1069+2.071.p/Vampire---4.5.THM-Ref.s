%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 275 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   21
%              Number of atoms          :  347 (1598 expanded)
%              Number of equality atoms :   65 ( 318 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f215,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f48,f211])).

fof(f211,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f210,f41])).

fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f210,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f191,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f191,plain,
    ( v1_xboole_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f189,f187])).

fof(f187,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f42,f186])).

fof(f186,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f185,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f185,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f184,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(subsumption_resolution,[],[f183,f85])).

fof(f85,plain,(
    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f82,f84])).

fof(f84,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f82,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f40,f80])).

fof(f80,plain,(
    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[],[f147,f80])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f146,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f145,f48])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f144,f47])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(subsumption_resolution,[],[f141,f46])).

fof(f46,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
      | ~ v1_funct_2(sK3,sK1,sK2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | v1_xboole_0(sK2)
      | ~ v1_funct_1(sK3)
      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) ) ),
    inference(superposition,[],[f106,f84])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | v1_xboole_0(X1)
      | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
      | k1_xboole_0 = sK1
      | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) ) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f42,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK1)
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f177,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f107,f73])).

fof(f73,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f71,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f50,f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ v1_funct_1(sK4)
      | ~ r2_hidden(X0,k1_relat_1(sK4))
      | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0) ) ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f78,plain,(
    v5_relat_1(sK4,sK0) ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f177,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f140,f135])).

fof(f135,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))
    | k1_xboole_0 = sK2
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f102,f75])).

fof(f75,plain,
    ( r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f57,f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f102,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3))
      | k1_xboole_0 = sK2 ) ),
    inference(forward_demodulation,[],[f101,f84])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,sK1,sK2)
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = sK2
      | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f140,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(X1,k1_relat_1(sK4)) ) ),
    inference(subsumption_resolution,[],[f137,f74])).

fof(f74,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f72,f56])).

fof(f72,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f47])).

fof(f137,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK3)
      | ~ r2_hidden(X1,k2_relat_1(sK3))
      | r2_hidden(X1,k1_relat_1(sK4)) ) ),
    inference(resolution,[],[f120,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f120,plain,(
    v5_relat_1(sK3,k1_relat_1(sK4)) ),
    inference(resolution,[],[f95,f65])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(subsumption_resolution,[],[f94,f74])).

fof(f94,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f93,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) ),
    inference(resolution,[],[f59,f85])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f48,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (24540)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (24540)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f242,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f215,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(backward_demodulation,[],[f48,f211])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    k1_xboole_0 = sK2),
% 0.21/0.46    inference(subsumption_resolution,[],[f210,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    k1_xboole_0 != sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.46    inference(flattening,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.46    inference(negated_conjecture,[],[f15])).
% 0.21/0.46  fof(f15,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.46    inference(resolution,[],[f191,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    v1_xboole_0(sK1) | k1_xboole_0 = sK2),
% 0.21/0.46    inference(subsumption_resolution,[],[f189,f187])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(backward_demodulation,[],[f42,f186])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(subsumption_resolution,[],[f185,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(subsumption_resolution,[],[f184,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    v1_funct_1(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(subsumption_resolution,[],[f183,f85])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.46    inference(backward_demodulation,[],[f82,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f64,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.46    inference(backward_demodulation,[],[f40,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.46    inference(resolution,[],[f63,f44])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(superposition,[],[f147,f80])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f146,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f145,f48])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f144,f47])).
% 0.21/0.46  fof(f144,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f141,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) )),
% 0.21/0.46    inference(superposition,[],[f106,f84])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f103,f41])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) )),
% 0.21/0.46    inference(resolution,[],[f62,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    m1_subset_1(sK5,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.46    inference(flattening,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    k1_xboole_0 = sK2 | v1_xboole_0(sK1) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.46    inference(resolution,[],[f177,f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f109,f43])).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f107,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    v1_relat_1(sK4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f71,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK4)),
% 0.21/0.46    inference(resolution,[],[f50,f44])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k1_funct_1(sK4,X0) = k7_partfun1(sK0,sK4,X0)) )),
% 0.21/0.46    inference(resolution,[],[f78,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    v5_relat_1(sK4,sK0)),
% 0.21/0.46    inference(resolution,[],[f65,f44])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.46    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f140,f135])).
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) | k1_xboole_0 = sK2 | v1_xboole_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f102,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    r2_hidden(sK5,sK1) | v1_xboole_0(sK1)),
% 0.21/0.46    inference(resolution,[],[f57,f39])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(k1_funct_1(sK3,X1),k2_relat_1(sK3)) | k1_xboole_0 = sK2) )),
% 0.21/0.46    inference(forward_demodulation,[],[f101,f84])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f100,f45])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    ( ! [X1] : (~v1_funct_1(sK3) | ~r2_hidden(X1,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f97,f46])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r2_hidden(X1,sK1) | k1_xboole_0 = sK2 | r2_hidden(k1_funct_1(sK3,X1),k2_relset_1(sK1,sK2,sK3))) )),
% 0.21/0.46    inference(resolution,[],[f66,f47])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.46    inference(flattening,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(X1,k1_relat_1(sK4))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f137,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    v1_relat_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f72,f56])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3)),
% 0.21/0.46    inference(resolution,[],[f50,f47])).
% 0.21/0.46  fof(f137,plain,(
% 0.21/0.46    ( ! [X1] : (~v1_relat_1(sK3) | ~r2_hidden(X1,k2_relat_1(sK3)) | r2_hidden(X1,k1_relat_1(sK4))) )),
% 0.21/0.46    inference(resolution,[],[f120,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.21/0.46    inference(resolution,[],[f95,f65])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))),
% 0.21/0.46    inference(subsumption_resolution,[],[f94,f74])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))),
% 0.21/0.46    inference(subsumption_resolution,[],[f93,f45])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4))))),
% 0.21/0.46    inference(resolution,[],[f59,f85])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ~v1_xboole_0(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (24540)------------------------------
% 0.21/0.46  % (24540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24540)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (24540)Memory used [KB]: 1918
% 0.21/0.46  % (24540)Time elapsed: 0.058 s
% 0.21/0.46  % (24540)------------------------------
% 0.21/0.46  % (24540)------------------------------
% 0.21/0.46  % (24529)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (24522)Success in time 0.094 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0994+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 4.07s
% Output     : Refutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 129 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   16
%              Number of atoms          :  201 ( 752 expanded)
%              Number of equality atoms :   64 ( 218 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8184,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8183,f5840])).

fof(f5840,plain,(
    v1_relat_1(sK40) ),
    inference(resolution,[],[f3530,f4178])).

fof(f4178,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1868])).

fof(f1868,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3530,plain,(
    m1_subset_1(sK40,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37))) ),
    inference(cnf_transformation,[],[f2706])).

fof(f2706,plain,
    ( k1_funct_1(sK40,sK38) != k1_funct_1(k6_relset_1(sK36,sK37,sK39,sK40),sK38)
    & k1_xboole_0 != sK37
    & r2_hidden(k1_funct_1(sK40,sK38),sK39)
    & r2_hidden(sK38,sK36)
    & m1_subset_1(sK40,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
    & v1_funct_2(sK40,sK36,sK37)
    & v1_funct_1(sK40) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37,sK38,sK39,sK40])],[f1555,f2705])).

fof(f2705,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK40,sK38) != k1_funct_1(k6_relset_1(sK36,sK37,sK39,sK40),sK38)
      & k1_xboole_0 != sK37
      & r2_hidden(k1_funct_1(sK40,sK38),sK39)
      & r2_hidden(sK38,sK36)
      & m1_subset_1(sK40,k1_zfmisc_1(k2_zfmisc_1(sK36,sK37)))
      & v1_funct_2(sK40,sK36,sK37)
      & v1_funct_1(sK40) ) ),
    introduced(choice_axiom,[])).

fof(f1555,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f1554])).

fof(f1554,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1519])).

fof(f1519,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1518])).

fof(f1518,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

fof(f8183,plain,(
    ~ v1_relat_1(sK40) ),
    inference(subsumption_resolution,[],[f8182,f3528])).

fof(f3528,plain,(
    v1_funct_1(sK40) ),
    inference(cnf_transformation,[],[f2706])).

fof(f8182,plain,
    ( ~ v1_funct_1(sK40)
    | ~ v1_relat_1(sK40) ),
    inference(subsumption_resolution,[],[f8120,f5915])).

fof(f5915,plain,(
    k1_funct_1(sK40,sK38) != k1_funct_1(k8_relat_1(sK39,sK40),sK38) ),
    inference(backward_demodulation,[],[f3534,f5823])).

fof(f5823,plain,(
    ! [X1] : k6_relset_1(sK36,sK37,X1,sK40) = k8_relat_1(X1,sK40) ),
    inference(resolution,[],[f3530,f3538])).

fof(f3538,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1560])).

fof(f1560,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1232])).

fof(f1232,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f3534,plain,(
    k1_funct_1(sK40,sK38) != k1_funct_1(k6_relset_1(sK36,sK37,sK39,sK40),sK38) ),
    inference(cnf_transformation,[],[f2706])).

fof(f8120,plain,
    ( k1_funct_1(sK40,sK38) = k1_funct_1(k8_relat_1(sK39,sK40),sK38)
    | ~ v1_funct_1(sK40)
    | ~ v1_relat_1(sK40) ),
    inference(resolution,[],[f6049,f3780])).

fof(f3780,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1692])).

fof(f1692,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1691])).

fof(f1691,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1048])).

fof(f1048,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f6049,plain,(
    r2_hidden(sK38,k1_relat_1(k8_relat_1(sK39,sK40))) ),
    inference(subsumption_resolution,[],[f6048,f5840])).

fof(f6048,plain,
    ( r2_hidden(sK38,k1_relat_1(k8_relat_1(sK39,sK40)))
    | ~ v1_relat_1(sK40) ),
    inference(subsumption_resolution,[],[f6022,f3531])).

fof(f3531,plain,(
    r2_hidden(sK38,sK36) ),
    inference(cnf_transformation,[],[f2706])).

fof(f6022,plain,
    ( ~ r2_hidden(sK38,sK36)
    | r2_hidden(sK38,k1_relat_1(k8_relat_1(sK39,sK40)))
    | ~ v1_relat_1(sK40) ),
    inference(backward_demodulation,[],[f5808,f6005])).

fof(f6005,plain,(
    sK36 = k1_relat_1(sK40) ),
    inference(forward_demodulation,[],[f5888,f5959])).

fof(f5959,plain,(
    sK36 = k1_relset_1(sK36,sK37,sK40) ),
    inference(subsumption_resolution,[],[f5958,f3533])).

fof(f3533,plain,(
    k1_xboole_0 != sK37 ),
    inference(cnf_transformation,[],[f2706])).

fof(f5958,plain,
    ( k1_xboole_0 = sK37
    | sK36 = k1_relset_1(sK36,sK37,sK40) ),
    inference(subsumption_resolution,[],[f5850,f3529])).

fof(f3529,plain,(
    v1_funct_2(sK40,sK36,sK37) ),
    inference(cnf_transformation,[],[f2706])).

fof(f5850,plain,
    ( ~ v1_funct_2(sK40,sK36,sK37)
    | k1_xboole_0 = sK37
    | sK36 = k1_relset_1(sK36,sK37,sK40) ),
    inference(resolution,[],[f3530,f4297])).

fof(f4297,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f3118])).

fof(f3118,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1928])).

fof(f1928,plain,(
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
    inference(flattening,[],[f1927])).

fof(f1927,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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

fof(f5888,plain,(
    k1_relat_1(sK40) = k1_relset_1(sK36,sK37,sK40) ),
    inference(resolution,[],[f3530,f5433])).

fof(f5433,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2636])).

fof(f2636,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5808,plain,
    ( r2_hidden(sK38,k1_relat_1(k8_relat_1(sK39,sK40)))
    | ~ r2_hidden(sK38,k1_relat_1(sK40))
    | ~ v1_relat_1(sK40) ),
    inference(subsumption_resolution,[],[f5763,f3528])).

fof(f5763,plain,
    ( r2_hidden(sK38,k1_relat_1(k8_relat_1(sK39,sK40)))
    | ~ r2_hidden(sK38,k1_relat_1(sK40))
    | ~ v1_funct_1(sK40)
    | ~ v1_relat_1(sK40) ),
    inference(resolution,[],[f3532,f3765])).

fof(f3765,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2818])).

fof(f2818,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2817])).

fof(f2817,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1676])).

fof(f1676,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1675])).

fof(f1675,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1047])).

fof(f1047,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f3532,plain,(
    r2_hidden(k1_funct_1(sK40,sK38),sK39) ),
    inference(cnf_transformation,[],[f2706])).
%------------------------------------------------------------------------------

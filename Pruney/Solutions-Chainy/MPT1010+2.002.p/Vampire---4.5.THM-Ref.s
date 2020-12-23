%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:50 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 123 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  273 ( 521 expanded)
%              Number of equality atoms :  106 ( 155 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,(
    sK1 != sK1 ),
    inference(resolution,[],[f147,f98])).

fof(f98,plain,(
    v5_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK1 != k1_funct_1(sK3,sK2)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f147,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,k1_tarski(X0))
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f48,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,sK0)
      | sK1 != X0
      | ~ v5_relat_1(sK3,k1_tarski(X0)) ) ),
    inference(forward_demodulation,[],[f145,f123])).

fof(f123,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f120,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,(
    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(subsumption_resolution,[],[f119,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(subsumption_resolution,[],[f95,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X0)) ) ),
    inference(superposition,[],[f85,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f93,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f119,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f145,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3))
      | ~ v5_relat_1(sK3,k1_tarski(X0)) ) ),
    inference(subsumption_resolution,[],[f144,f45])).

% (24687)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (24688)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f144,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3))
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f138,f92])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3))
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f49,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v5_relat_1(X0,k1_tarski(X2))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v5_relat_1(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(k1_funct_1(X1,X0),X2)
      | ~ v5_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f55,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

% (24706)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f49,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n012.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 16:12:52 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.11/0.40  % (24693)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.11/0.40  % (24694)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.11/0.40  % (24695)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.11/0.41  % (24684)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.11/0.41  % (24686)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.11/0.41  % (24705)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.11/0.42  % (24692)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.11/0.42  % (24685)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.11/0.42  % (24710)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.11/0.42  % (24683)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.11/0.42  % (24703)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.11/0.42  % (24697)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.11/0.42  % (24696)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.11/0.42  % (24698)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.11/0.42  % (24707)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.11/0.42  % (24692)Refutation found. Thanks to Tanya!
% 0.11/0.42  % SZS status Theorem for theBenchmark
% 0.11/0.42  % SZS output start Proof for theBenchmark
% 0.11/0.42  fof(f149,plain,(
% 0.11/0.42    $false),
% 0.11/0.42    inference(trivial_inequality_removal,[],[f148])).
% 0.11/0.42  fof(f148,plain,(
% 0.11/0.42    sK1 != sK1),
% 0.11/0.42    inference(resolution,[],[f147,f98])).
% 0.11/0.42  fof(f98,plain,(
% 0.11/0.42    v5_relat_1(sK3,k1_tarski(sK1))),
% 0.11/0.42    inference(resolution,[],[f69,f47])).
% 0.11/0.42  fof(f47,plain,(
% 0.11/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.11/0.42    inference(cnf_transformation,[],[f36])).
% 0.11/0.42  fof(f36,plain,(
% 0.11/0.42    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 0.11/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f35])).
% 0.11/0.42  fof(f35,plain,(
% 0.11/0.42    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.11/0.42    introduced(choice_axiom,[])).
% 0.11/0.42  fof(f24,plain,(
% 0.11/0.42    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.11/0.42    inference(flattening,[],[f23])).
% 0.11/0.42  fof(f23,plain,(
% 0.11/0.42    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.11/0.42    inference(ennf_transformation,[],[f21])).
% 0.11/0.42  fof(f21,negated_conjecture,(
% 0.11/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.11/0.42    inference(negated_conjecture,[],[f20])).
% 0.11/0.42  fof(f20,conjecture,(
% 0.11/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.11/0.42  fof(f69,plain,(
% 0.11/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f32])).
% 0.11/0.42  fof(f32,plain,(
% 0.11/0.42    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.42    inference(ennf_transformation,[],[f22])).
% 0.11/0.42  fof(f22,plain,(
% 0.11/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.11/0.42    inference(pure_predicate_removal,[],[f17])).
% 0.11/0.42  fof(f17,axiom,(
% 0.11/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.11/0.42  fof(f147,plain,(
% 0.11/0.42    ( ! [X0] : (~v5_relat_1(sK3,k1_tarski(X0)) | sK1 != X0) )),
% 0.11/0.42    inference(subsumption_resolution,[],[f146,f48])).
% 0.11/0.42  fof(f48,plain,(
% 0.11/0.42    r2_hidden(sK2,sK0)),
% 0.11/0.42    inference(cnf_transformation,[],[f36])).
% 0.11/0.42  fof(f146,plain,(
% 0.11/0.42    ( ! [X0] : (~r2_hidden(sK2,sK0) | sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0))) )),
% 0.11/0.42    inference(forward_demodulation,[],[f145,f123])).
% 0.11/0.42  fof(f123,plain,(
% 0.11/0.42    sK0 = k1_relat_1(sK3)),
% 0.11/0.42    inference(subsumption_resolution,[],[f121,f47])).
% 0.11/0.42  fof(f121,plain,(
% 0.11/0.42    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.11/0.42    inference(superposition,[],[f120,f68])).
% 0.11/0.42  fof(f68,plain,(
% 0.11/0.42    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f31])).
% 0.11/0.42  fof(f31,plain,(
% 0.11/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.42    inference(ennf_transformation,[],[f18])).
% 0.11/0.42  fof(f18,axiom,(
% 0.11/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.11/0.42  fof(f120,plain,(
% 0.11/0.42    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.11/0.42    inference(subsumption_resolution,[],[f119,f96])).
% 0.11/0.42  fof(f96,plain,(
% 0.11/0.42    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.11/0.42    inference(subsumption_resolution,[],[f95,f80])).
% 0.11/0.42  fof(f80,plain,(
% 0.11/0.42    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.11/0.42    inference(equality_resolution,[],[f58])).
% 0.11/0.42  fof(f58,plain,(
% 0.11/0.42    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.11/0.42    inference(cnf_transformation,[],[f38])).
% 0.11/0.42  fof(f38,plain,(
% 0.11/0.42    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.11/0.42    inference(flattening,[],[f37])).
% 0.11/0.42  fof(f37,plain,(
% 0.11/0.42    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.11/0.42    inference(nnf_transformation,[],[f1])).
% 0.11/0.42  fof(f1,axiom,(
% 0.11/0.42    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.11/0.42  fof(f95,plain,(
% 0.11/0.42    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | ~r1_tarski(k1_tarski(X0),k1_tarski(X0))) )),
% 0.11/0.42    inference(superposition,[],[f85,f94])).
% 0.11/0.42  fof(f94,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.11/0.42    inference(forward_demodulation,[],[f93,f50])).
% 0.11/0.42  fof(f50,plain,(
% 0.11/0.42    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.11/0.42    inference(cnf_transformation,[],[f4])).
% 0.11/0.42  fof(f4,axiom,(
% 0.11/0.42    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.11/0.42  fof(f93,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 0.11/0.42    inference(superposition,[],[f53,f54])).
% 0.11/0.42  fof(f54,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.11/0.42    inference(cnf_transformation,[],[f25])).
% 0.11/0.42  fof(f25,plain,(
% 0.11/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.11/0.42    inference(ennf_transformation,[],[f3])).
% 0.11/0.42  fof(f3,axiom,(
% 0.11/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.11/0.42  fof(f53,plain,(
% 0.11/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f2])).
% 0.11/0.42  fof(f2,axiom,(
% 0.11/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.11/0.42  fof(f85,plain,(
% 0.11/0.42    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.11/0.42    inference(equality_resolution,[],[f64])).
% 0.11/0.42  fof(f64,plain,(
% 0.11/0.42    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.11/0.42    inference(cnf_transformation,[],[f43])).
% 0.11/0.42  fof(f43,plain,(
% 0.11/0.42    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.11/0.42    inference(nnf_transformation,[],[f13])).
% 0.11/0.42  fof(f13,axiom,(
% 0.11/0.42    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.11/0.42  fof(f119,plain,(
% 0.11/0.42    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.11/0.42    inference(subsumption_resolution,[],[f118,f46])).
% 0.11/0.42  fof(f46,plain,(
% 0.11/0.42    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.11/0.42    inference(cnf_transformation,[],[f36])).
% 0.11/0.42  fof(f118,plain,(
% 0.11/0.42    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 0.11/0.42    inference(resolution,[],[f70,f47])).
% 0.11/0.42  fof(f70,plain,(
% 0.11/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.11/0.42    inference(cnf_transformation,[],[f44])).
% 0.11/0.42  fof(f44,plain,(
% 0.11/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.42    inference(nnf_transformation,[],[f34])).
% 0.11/0.42  fof(f34,plain,(
% 0.11/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.42    inference(flattening,[],[f33])).
% 0.11/0.42  fof(f33,plain,(
% 0.11/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.42    inference(ennf_transformation,[],[f19])).
% 0.11/0.42  fof(f19,axiom,(
% 0.11/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.11/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.11/0.42  fof(f145,plain,(
% 0.11/0.42    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v5_relat_1(sK3,k1_tarski(X0))) )),
% 0.11/0.42    inference(subsumption_resolution,[],[f144,f45])).
% 0.11/0.42  % (24687)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.11/0.42  % (24688)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.11/0.43  fof(f45,plain,(
% 0.11/0.43    v1_funct_1(sK3)),
% 0.11/0.43    inference(cnf_transformation,[],[f36])).
% 0.11/0.43  fof(f144,plain,(
% 0.11/0.43    ( ! [X0] : (sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_funct_1(sK3)) )),
% 0.11/0.43    inference(subsumption_resolution,[],[f138,f92])).
% 0.11/0.43  fof(f92,plain,(
% 0.11/0.43    v1_relat_1(sK3)),
% 0.11/0.43    inference(resolution,[],[f67,f47])).
% 0.11/0.43  fof(f67,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f30])).
% 0.11/0.43  fof(f30,plain,(
% 0.11/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.11/0.43    inference(ennf_transformation,[],[f16])).
% 0.11/0.43  fof(f16,axiom,(
% 0.11/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.11/0.43  fof(f138,plain,(
% 0.11/0.43    ( ! [X0] : (sK1 != X0 | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_funct_1(sK3)) )),
% 0.11/0.43    inference(superposition,[],[f49,f110])).
% 0.11/0.43  fof(f110,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v5_relat_1(X0,k1_tarski(X2)) | ~v1_funct_1(X0)) )),
% 0.11/0.43    inference(resolution,[],[f105,f84])).
% 0.11/0.43  fof(f84,plain,(
% 0.11/0.43    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.11/0.43    inference(equality_resolution,[],[f60])).
% 0.11/0.43  fof(f60,plain,(
% 0.11/0.43    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.11/0.43    inference(cnf_transformation,[],[f42])).
% 0.11/0.43  fof(f42,plain,(
% 0.11/0.43    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.11/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.11/0.43  fof(f41,plain,(
% 0.11/0.43    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.11/0.43    introduced(choice_axiom,[])).
% 0.11/0.43  fof(f40,plain,(
% 0.11/0.43    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.11/0.43    inference(rectify,[],[f39])).
% 0.11/0.43  fof(f39,plain,(
% 0.11/0.43    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.11/0.43    inference(nnf_transformation,[],[f5])).
% 0.11/0.43  fof(f5,axiom,(
% 0.11/0.43    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.11/0.43  fof(f105,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X0),X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v5_relat_1(X1,X2)) )),
% 0.11/0.43    inference(duplicate_literal_removal,[],[f104])).
% 0.11/0.43  fof(f104,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),X2) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 0.11/0.43    inference(resolution,[],[f55,f56])).
% 0.11/0.43  fof(f56,plain,(
% 0.11/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f29])).
% 0.11/0.43  fof(f29,plain,(
% 0.11/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.11/0.43    inference(flattening,[],[f28])).
% 0.11/0.43  fof(f28,plain,(
% 0.11/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.11/0.43    inference(ennf_transformation,[],[f14])).
% 0.11/0.43  fof(f14,axiom,(
% 0.11/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 0.11/0.43  fof(f55,plain,(
% 0.11/0.43    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.11/0.43    inference(cnf_transformation,[],[f27])).
% 0.11/0.43  % (24706)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.11/0.43  fof(f27,plain,(
% 0.11/0.43    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.11/0.43    inference(flattening,[],[f26])).
% 0.11/0.43  fof(f26,plain,(
% 0.11/0.43    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.11/0.43    inference(ennf_transformation,[],[f15])).
% 0.11/0.43  fof(f15,axiom,(
% 0.11/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.11/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.11/0.43  fof(f49,plain,(
% 0.11/0.43    sK1 != k1_funct_1(sK3,sK2)),
% 0.11/0.43    inference(cnf_transformation,[],[f36])).
% 0.11/0.43  % SZS output end Proof for theBenchmark
% 0.11/0.43  % (24692)------------------------------
% 0.11/0.43  % (24692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.43  % (24692)Termination reason: Refutation
% 0.11/0.43  
% 0.11/0.43  % (24692)Memory used [KB]: 1791
% 0.11/0.43  % (24692)Time elapsed: 0.100 s
% 0.11/0.43  % (24692)------------------------------
% 0.11/0.43  % (24692)------------------------------
% 0.11/0.43  % (24702)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.11/0.43  % (24699)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.11/0.43  % (24684)Refutation not found, incomplete strategy% (24684)------------------------------
% 0.11/0.43  % (24684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.43  % (24684)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.43  
% 0.11/0.43  % (24684)Memory used [KB]: 1663
% 0.11/0.43  % (24684)Time elapsed: 0.118 s
% 0.11/0.43  % (24684)------------------------------
% 0.11/0.43  % (24684)------------------------------
% 0.11/0.43  % (24682)Success in time 0.167 s
%------------------------------------------------------------------------------

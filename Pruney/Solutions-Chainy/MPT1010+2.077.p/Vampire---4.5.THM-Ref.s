%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 ( 462 expanded)
%              Number of equality atoms :   92 ( 141 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f42])).

fof(f42,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f32])).

fof(f32,plain,
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

fof(f150,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f117,f145])).

fof(f145,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f143,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f142,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f142,plain,(
    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(subsumption_resolution,[],[f141,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f77,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f87,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f141,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(subsumption_resolution,[],[f140,f40])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f140,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f117,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(superposition,[],[f43,f107])).

fof(f107,plain,(
    ! [X6] :
      ( sK1 = k1_funct_1(sK3,X6)
      | ~ r2_hidden(X6,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f106,f86])).

fof(f86,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f106,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3)
      | sK1 = k1_funct_1(sK3,X6) ) ),
    inference(subsumption_resolution,[],[f102,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_relat_1(sK3))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK1 = k1_funct_1(sK3,X6) ) ),
    inference(resolution,[],[f76,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK3)
      | sK1 = X0 ) ),
    inference(resolution,[],[f69,f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1)))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f43,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (10586)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (10575)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (10576)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (10569)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (10578)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (10571)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (10590)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (10580)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (10582)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (10577)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (10577)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (10596)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (10570)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (10572)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (10573)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (10574)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (10594)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (10582)Refutation not found, incomplete strategy% (10582)------------------------------
% 1.36/0.54  % (10582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (10582)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (10582)Memory used [KB]: 1791
% 1.36/0.54  % (10582)Time elapsed: 0.079 s
% 1.36/0.54  % (10582)------------------------------
% 1.36/0.54  % (10582)------------------------------
% 1.36/0.54  % (10587)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.54  % (10568)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.54  % (10569)Refutation not found, incomplete strategy% (10569)------------------------------
% 1.36/0.54  % (10569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (10569)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (10569)Memory used [KB]: 1791
% 1.36/0.54  % (10569)Time elapsed: 0.124 s
% 1.36/0.54  % (10569)------------------------------
% 1.36/0.54  % (10569)------------------------------
% 1.36/0.54  % (10588)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.54  % (10591)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.55  % (10592)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.55  % (10597)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.55  % (10585)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.55  % (10595)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.55  % (10584)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f159,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f150,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    r2_hidden(sK2,sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.36/0.55    inference(flattening,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.36/0.55    inference(ennf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.36/0.55    inference(negated_conjecture,[],[f20])).
% 1.36/0.55  fof(f20,conjecture,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.36/0.55  fof(f150,plain,(
% 1.36/0.55    ~r2_hidden(sK2,sK0)),
% 1.36/0.55    inference(backward_demodulation,[],[f117,f145])).
% 1.36/0.55  fof(f145,plain,(
% 1.36/0.55    sK0 = k1_relat_1(sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f143,f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f143,plain,(
% 1.36/0.55    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.36/0.55    inference(superposition,[],[f142,f60])).
% 1.36/0.55  fof(f60,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.55  fof(f142,plain,(
% 1.36/0.55    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f141,f89])).
% 1.36/0.55  fof(f89,plain,(
% 1.36/0.55    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.36/0.55    inference(backward_demodulation,[],[f77,f88])).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f87,f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.36/0.55  fof(f87,plain,(
% 1.36/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.36/0.55    inference(superposition,[],[f54,f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.55    inference(rectify,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.36/0.55    inference(equality_resolution,[],[f56])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.36/0.55    inference(nnf_transformation,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.36/0.55  fof(f141,plain,(
% 1.36/0.55    k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.36/0.55    inference(subsumption_resolution,[],[f140,f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f140,plain,(
% 1.36/0.55    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.36/0.55    inference(resolution,[],[f61,f41])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(nnf_transformation,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(flattening,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f19])).
% 1.36/0.55  fof(f19,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.55  fof(f117,plain,(
% 1.36/0.55    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.36/0.55    inference(trivial_inequality_removal,[],[f113])).
% 1.36/0.55  fof(f113,plain,(
% 1.36/0.55    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.36/0.55    inference(superposition,[],[f43,f107])).
% 1.36/0.55  fof(f107,plain,(
% 1.36/0.55    ( ! [X6] : (sK1 = k1_funct_1(sK3,X6) | ~r2_hidden(X6,k1_relat_1(sK3))) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f106,f86])).
% 1.36/0.55  fof(f86,plain,(
% 1.36/0.55    v1_relat_1(sK3)),
% 1.36/0.55    inference(resolution,[],[f59,f41])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.55  fof(f106,plain,(
% 1.36/0.55    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | sK1 = k1_funct_1(sK3,X6)) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f102,f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    v1_funct_1(sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f102,plain,(
% 1.36/0.55    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK1 = k1_funct_1(sK3,X6)) )),
% 1.36/0.55    inference(resolution,[],[f76,f94])).
% 1.36/0.55  fof(f94,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK3) | sK1 = X0) )),
% 1.36/0.55    inference(resolution,[],[f69,f90])).
% 1.36/0.55  fof(f90,plain,(
% 1.36/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,k1_tarski(sK1))) | ~r2_hidden(X0,sK3)) )),
% 1.36/0.55    inference(resolution,[],[f55,f41])).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) )),
% 1.36/0.55    inference(cnf_transformation,[],[f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.36/0.55    inference(flattening,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.36/0.55    inference(nnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.36/0.55  fof(f76,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(equality_resolution,[],[f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(nnf_transformation,[],[f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    sK1 != k1_funct_1(sK3,sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (10577)------------------------------
% 1.36/0.55  % (10577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (10577)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (10577)Memory used [KB]: 1791
% 1.36/0.55  % (10577)Time elapsed: 0.121 s
% 1.36/0.55  % (10577)------------------------------
% 1.36/0.55  % (10577)------------------------------
% 1.36/0.55  % (10567)Success in time 0.186 s
%------------------------------------------------------------------------------

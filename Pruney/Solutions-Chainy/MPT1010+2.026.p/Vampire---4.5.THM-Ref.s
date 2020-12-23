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
% DateTime   : Thu Dec  3 13:04:54 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 208 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  291 ( 970 expanded)
%              Number of equality atoms :  121 ( 311 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(resolution,[],[f191,f42])).

fof(f42,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).

fof(f26,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f191,plain,(
    ! [X2] : ~ r2_hidden(X2,sK0) ),
    inference(resolution,[],[f189,f140])).

fof(f140,plain,(
    ! [X5] :
      ( ~ v5_relat_1(sK3,k1_xboole_0)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f138,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_xboole_0,sK1)
      | ~ v5_relat_1(sK3,k1_xboole_0)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f95,f132])).

fof(f132,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | ~ v5_relat_1(sK3,k1_xboole_0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f131,f39])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v5_relat_1(sK3,k1_xboole_0)
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f130,f103])).

fof(f103,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ v5_relat_1(sK3,k1_xboole_0)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(sK3)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f122,f128])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f126,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(superposition,[],[f125,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f125,plain,
    ( sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f124,f40])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1)
    | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f118,f44])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f95,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),X0) ),
    inference(resolution,[],[f89,f48])).

fof(f89,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f80,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f80,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f189,plain,(
    v5_relat_1(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f104,f186])).

fof(f186,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f185,f42])).

fof(f185,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f182,f128])).

fof(f182,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f176,f104])).

fof(f176,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK3,k1_tarski(X0))
      | sK1 != X0
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f175,f103])).

fof(f175,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f169,f39])).

fof(f169,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_funct_1(sK3)
      | ~ v5_relat_1(sK3,k1_tarski(X0))
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(sK2,k1_relat_1(sK3)) ) ),
    inference(superposition,[],[f43,f121])).

fof(f121,plain,(
    ! [X14,X12,X13] :
      ( k1_funct_1(X13,X12) = X14
      | ~ v1_funct_1(X13)
      | ~ v5_relat_1(X13,k1_tarski(X14))
      | ~ v1_relat_1(X13)
      | ~ r2_hidden(X12,k1_relat_1(X13)) ) ),
    inference(resolution,[],[f47,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f81,f45])).

fof(f81,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,(
    v5_relat_1(sK3,k1_tarski(sK1)) ),
    inference(resolution,[],[f51,f41])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (7578)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (7593)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (7591)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (7576)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.40/0.57  % (7586)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.57  % (7584)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.57  % (7575)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.40/0.57  % (7591)Refutation not found, incomplete strategy% (7591)------------------------------
% 1.40/0.57  % (7591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (7591)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (7591)Memory used [KB]: 10746
% 1.40/0.57  % (7591)Time elapsed: 0.152 s
% 1.40/0.57  % (7591)------------------------------
% 1.40/0.57  % (7591)------------------------------
% 1.40/0.58  % (7593)Refutation not found, incomplete strategy% (7593)------------------------------
% 1.40/0.58  % (7593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (7588)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.68/0.58  % (7584)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.58  % SZS output start Proof for theBenchmark
% 1.68/0.58  fof(f199,plain,(
% 1.68/0.58    $false),
% 1.68/0.58    inference(resolution,[],[f191,f42])).
% 1.68/0.58  fof(f42,plain,(
% 1.68/0.58    r2_hidden(sK2,sK0)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).
% 1.68/0.58  fof(f26,plain,(
% 1.68/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f16,plain,(
% 1.68/0.58    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.68/0.58    inference(flattening,[],[f15])).
% 1.68/0.58  fof(f15,plain,(
% 1.68/0.58    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.68/0.58    inference(ennf_transformation,[],[f13])).
% 1.68/0.58  fof(f13,negated_conjecture,(
% 1.68/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.68/0.58    inference(negated_conjecture,[],[f12])).
% 1.68/0.58  fof(f12,conjecture,(
% 1.68/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.68/0.58  fof(f191,plain,(
% 1.68/0.58    ( ! [X2] : (~r2_hidden(X2,sK0)) )),
% 1.68/0.58    inference(resolution,[],[f189,f140])).
% 1.68/0.58  fof(f140,plain,(
% 1.68/0.58    ( ! [X5] : (~v5_relat_1(sK3,k1_xboole_0) | ~r2_hidden(X5,sK0)) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f138,f44])).
% 1.68/0.58  fof(f44,plain,(
% 1.68/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.68/0.58  fof(f138,plain,(
% 1.68/0.58    ( ! [X5] : (~r1_tarski(k1_xboole_0,sK1) | ~v5_relat_1(sK3,k1_xboole_0) | ~r2_hidden(X5,sK0)) )),
% 1.68/0.58    inference(superposition,[],[f95,f132])).
% 1.68/0.58  fof(f132,plain,(
% 1.68/0.58    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | ~v5_relat_1(sK3,k1_xboole_0) | ~r2_hidden(X0,sK0)) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f131,f39])).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    v1_funct_1(sK3)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f131,plain,(
% 1.68/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v5_relat_1(sK3,k1_xboole_0) | ~v1_funct_1(sK3) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f130,f103])).
% 1.68/0.58  fof(f103,plain,(
% 1.68/0.58    v1_relat_1(sK3)),
% 1.68/0.58    inference(resolution,[],[f49,f41])).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f49,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f20])).
% 1.68/0.58  fof(f20,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.68/0.58  fof(f130,plain,(
% 1.68/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v5_relat_1(sK3,k1_xboole_0) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.68/0.58    inference(superposition,[],[f122,f128])).
% 1.68/0.58  fof(f128,plain,(
% 1.68/0.58    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.68/0.58    inference(subsumption_resolution,[],[f126,f41])).
% 1.68/0.58  fof(f126,plain,(
% 1.68/0.58    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k1_tarski(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.68/0.58    inference(superposition,[],[f125,f50])).
% 1.68/0.58  fof(f50,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f21])).
% 1.68/0.58  fof(f21,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f10])).
% 1.68/0.58  fof(f10,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.68/0.58  fof(f125,plain,(
% 1.68/0.58    sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.68/0.58    inference(subsumption_resolution,[],[f124,f40])).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f124,plain,(
% 1.68/0.58    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_relset_1(sK0,k1_tarski(sK1),sK3)),
% 1.68/0.58    inference(resolution,[],[f52,f41])).
% 1.68/0.58  fof(f52,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.68/0.58    inference(cnf_transformation,[],[f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(nnf_transformation,[],[f24])).
% 1.68/0.58  fof(f24,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(flattening,[],[f23])).
% 1.68/0.58  fof(f23,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f11])).
% 1.68/0.58  fof(f11,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.68/0.58  fof(f122,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 1.68/0.58    inference(resolution,[],[f118,f44])).
% 1.68/0.58  fof(f118,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 1.68/0.58    inference(resolution,[],[f47,f48])).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f19])).
% 1.68/0.58  fof(f19,plain,(
% 1.68/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.68/0.58    inference(ennf_transformation,[],[f7])).
% 1.68/0.58  fof(f7,axiom,(
% 1.68/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.68/0.58  fof(f47,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f18])).
% 1.68/0.58  fof(f18,plain,(
% 1.68/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.68/0.58    inference(flattening,[],[f17])).
% 1.68/0.58  fof(f17,plain,(
% 1.68/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.68/0.58    inference(ennf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.68/0.58  fof(f95,plain,(
% 1.68/0.58    ( ! [X0] : (~r1_tarski(k1_tarski(X0),X0)) )),
% 1.68/0.58    inference(resolution,[],[f89,f48])).
% 1.68/0.58  fof(f89,plain,(
% 1.68/0.58    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.68/0.58    inference(superposition,[],[f80,f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f4])).
% 1.68/0.58  fof(f4,axiom,(
% 1.68/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.58  fof(f80,plain,(
% 1.68/0.58    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.68/0.58    inference(equality_resolution,[],[f79])).
% 1.68/0.58  fof(f79,plain,(
% 1.68/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.68/0.58    inference(equality_resolution,[],[f59])).
% 1.68/0.58  fof(f59,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f33])).
% 1.68/0.58  fof(f33,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.68/0.58    introduced(choice_axiom,[])).
% 1.68/0.58  fof(f31,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(rectify,[],[f30])).
% 1.68/0.58  fof(f30,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(flattening,[],[f29])).
% 1.68/0.58  fof(f29,plain,(
% 1.68/0.58    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.68/0.58    inference(nnf_transformation,[],[f3])).
% 1.68/0.58  fof(f3,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.68/0.58  fof(f189,plain,(
% 1.68/0.58    v5_relat_1(sK3,k1_xboole_0)),
% 1.68/0.58    inference(backward_demodulation,[],[f104,f186])).
% 1.68/0.58  fof(f186,plain,(
% 1.68/0.58    k1_xboole_0 = k1_tarski(sK1)),
% 1.68/0.58    inference(subsumption_resolution,[],[f185,f42])).
% 1.68/0.58  fof(f185,plain,(
% 1.68/0.58    ~r2_hidden(sK2,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 1.68/0.58    inference(superposition,[],[f182,f128])).
% 1.68/0.58  fof(f182,plain,(
% 1.68/0.58    ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.68/0.58    inference(trivial_inequality_removal,[],[f178])).
% 1.68/0.58  fof(f178,plain,(
% 1.68/0.58    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3))),
% 1.68/0.58    inference(resolution,[],[f176,f104])).
% 1.68/0.58  fof(f176,plain,(
% 1.68/0.58    ( ! [X0] : (~v5_relat_1(sK3,k1_tarski(X0)) | sK1 != X0 | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f175,f103])).
% 1.68/0.58  fof(f175,plain,(
% 1.68/0.58    ( ! [X0] : (sK1 != X0 | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f169,f39])).
% 1.68/0.58  fof(f169,plain,(
% 1.68/0.58    ( ! [X0] : (sK1 != X0 | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,k1_tarski(X0)) | ~v1_relat_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3))) )),
% 1.68/0.58    inference(superposition,[],[f43,f121])).
% 1.68/0.58  fof(f121,plain,(
% 1.68/0.58    ( ! [X14,X12,X13] : (k1_funct_1(X13,X12) = X14 | ~v1_funct_1(X13) | ~v5_relat_1(X13,k1_tarski(X14)) | ~v1_relat_1(X13) | ~r2_hidden(X12,k1_relat_1(X13))) )),
% 1.68/0.58    inference(resolution,[],[f47,f108])).
% 1.68/0.58  fof(f108,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f107])).
% 1.68/0.58  fof(f107,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 1.68/0.58    inference(superposition,[],[f81,f45])).
% 1.68/0.58  fof(f81,plain,(
% 1.68/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.68/0.58    inference(equality_resolution,[],[f58])).
% 1.68/0.58  fof(f58,plain,(
% 1.68/0.58    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f33])).
% 1.68/0.58  fof(f43,plain,(
% 1.68/0.58    sK1 != k1_funct_1(sK3,sK2)),
% 1.68/0.58    inference(cnf_transformation,[],[f27])).
% 1.68/0.58  fof(f104,plain,(
% 1.68/0.58    v5_relat_1(sK3,k1_tarski(sK1))),
% 1.68/0.58    inference(resolution,[],[f51,f41])).
% 1.68/0.58  fof(f51,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f22])).
% 1.68/0.58  fof(f22,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/0.58    inference(ennf_transformation,[],[f14])).
% 1.68/0.58  fof(f14,plain,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.68/0.58    inference(pure_predicate_removal,[],[f9])).
% 1.68/0.58  fof(f9,axiom,(
% 1.68/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (7584)------------------------------
% 1.68/0.58  % (7584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (7584)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (7584)Memory used [KB]: 1791
% 1.68/0.58  % (7584)Time elapsed: 0.158 s
% 1.68/0.58  % (7584)------------------------------
% 1.68/0.58  % (7584)------------------------------
% 1.68/0.59  % (7574)Success in time 0.222 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:04 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 206 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  288 ( 686 expanded)
%              Number of equality atoms :   96 ( 254 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(subsumption_resolution,[],[f231,f115])).

fof(f115,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f231,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f101,f169])).

fof(f169,plain,(
    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f168,f101])).

fof(f168,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f51,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK1 != k1_funct_1(sK3,sK2)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f31])).

fof(f31,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f165,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK1 = k1_funct_1(sK3,sK2)
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(resolution,[],[f164,f50])).

fof(f50,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f164,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK1 = k1_funct_1(sK3,X3)
      | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ) ),
    inference(superposition,[],[f133,f161])).

fof(f161,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f159,f86])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f158,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f158,plain,
    ( sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f157,f87])).

fof(f87,plain,(
    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) ),
    inference(resolution,[],[f69,f86])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f132,f102])).

fof(f102,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f131,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f59,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f131,plain,(
    ! [X0] :
      ( m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f130,f86])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f129,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

% (2540)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (2523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (2520)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (2532)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X0)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X1),X0) ) ),
    inference(subsumption_resolution,[],[f128,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X0)
      | ~ r2_hidden(X1,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X1),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ) ),
    inference(resolution,[],[f127,f86])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
      | ~ v5_relat_1(sK3,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f126,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | m1_subset_1(k1_funct_1(sK3,X0),X1)
      | ~ v5_relat_1(sK3,X1)
      | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f101,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2521)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (2541)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (2513)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (2529)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (2524)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (2525)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (2535)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (2514)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (2522)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (2537)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (2527)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (2516)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (2514)Refutation not found, incomplete strategy% (2514)------------------------------
% 0.22/0.53  % (2514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2514)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2514)Memory used [KB]: 1663
% 0.22/0.53  % (2514)Time elapsed: 0.092 s
% 0.22/0.53  % (2514)------------------------------
% 0.22/0.53  % (2514)------------------------------
% 0.22/0.53  % (2528)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (2526)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (2538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (2539)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (2515)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (2527)Refutation not found, incomplete strategy% (2527)------------------------------
% 0.22/0.53  % (2527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2527)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2527)Memory used [KB]: 1791
% 0.22/0.53  % (2527)Time elapsed: 0.083 s
% 1.34/0.53  % (2527)------------------------------
% 1.34/0.53  % (2527)------------------------------
% 1.34/0.53  % (2533)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (2519)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (2530)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (2531)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (2529)Refutation not found, incomplete strategy% (2529)------------------------------
% 1.34/0.54  % (2529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (2529)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (2529)Memory used [KB]: 10746
% 1.34/0.54  % (2529)Time elapsed: 0.132 s
% 1.34/0.54  % (2529)------------------------------
% 1.34/0.54  % (2529)------------------------------
% 1.34/0.54  % (2535)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (2536)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.54  % (2518)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  % (2517)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f237,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(subsumption_resolution,[],[f231,f115])).
% 1.34/0.54  fof(f115,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.34/0.54    inference(resolution,[],[f64,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,axiom,(
% 1.34/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.34/0.54  fof(f231,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_xboole_0)),
% 1.34/0.54    inference(superposition,[],[f101,f169])).
% 1.34/0.54  fof(f169,plain,(
% 1.34/0.54    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.34/0.54    inference(resolution,[],[f168,f101])).
% 1.34/0.54  fof(f168,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f165,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    sK1 != k1_funct_1(sK3,sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK1 != k1_funct_1(sK3,sK2) & r2_hidden(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.34/0.54    inference(flattening,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.34/0.54    inference(ennf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.34/0.54    inference(negated_conjecture,[],[f16])).
% 1.34/0.54  fof(f16,conjecture,(
% 1.34/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.34/0.54  fof(f165,plain,(
% 1.34/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,sK2) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.34/0.54    inference(resolution,[],[f164,f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    r2_hidden(sK2,sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f164,plain,(
% 1.34/0.54    ( ! [X4,X3] : (~r2_hidden(X3,sK0) | ~r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,X3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)) )),
% 1.34/0.54    inference(superposition,[],[f133,f161])).
% 1.34/0.54  fof(f161,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.34/0.54    inference(subsumption_resolution,[],[f159,f86])).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.34/0.54    inference(definition_unfolding,[],[f49,f85])).
% 1.34/0.54  fof(f85,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f53,f84])).
% 1.34/0.54  fof(f84,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f58,f65])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f53,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f159,plain,(
% 1.34/0.54    sK0 = k1_relat_1(sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.34/0.54    inference(superposition,[],[f158,f66])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.54  fof(f158,plain,(
% 1.34/0.54    sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.34/0.54    inference(subsumption_resolution,[],[f157,f87])).
% 1.34/0.54  fof(f87,plain,(
% 1.34/0.54    v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.34/0.54    inference(definition_unfolding,[],[f48,f85])).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.34/0.54    inference(cnf_transformation,[],[f32])).
% 1.34/0.54  fof(f157,plain,(
% 1.34/0.54    ~v1_funct_2(sK3,sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK3)),
% 1.34/0.54    inference(resolution,[],[f69,f86])).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(nnf_transformation,[],[f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(flattening,[],[f26])).
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.34/0.54  fof(f133,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = k1_funct_1(sK3,X0)) )),
% 1.34/0.54    inference(resolution,[],[f132,f102])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.34/0.54    inference(equality_resolution,[],[f91])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.34/0.54    inference(definition_unfolding,[],[f60,f85])).
% 1.34/0.54  fof(f60,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(rectify,[],[f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.54    inference(nnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.34/0.54  fof(f132,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.34/0.54    inference(resolution,[],[f131,f118])).
% 1.34/0.54  fof(f118,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) )),
% 1.34/0.54    inference(resolution,[],[f59,f55])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(rectify,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.54    inference(nnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.34/0.54    inference(flattening,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.34/0.54  fof(f131,plain,(
% 1.34/0.54    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.34/0.54    inference(resolution,[],[f130,f86])).
% 1.34/0.54  fof(f130,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.34/0.54    inference(resolution,[],[f129,f68])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  % (2540)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.55  % (2523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (2520)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.55  % (2532)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.55  fof(f13,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.55  fof(f129,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0)) )),
% 1.34/0.55    inference(subsumption_resolution,[],[f128,f57])).
% 1.34/0.55  fof(f57,plain,(
% 1.34/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f10])).
% 1.34/0.55  fof(f10,axiom,(
% 1.34/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.55  fof(f128,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) )),
% 1.34/0.55    inference(resolution,[],[f127,f86])).
% 1.34/0.55  fof(f127,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~v5_relat_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v1_relat_1(X2)) )),
% 1.34/0.55    inference(resolution,[],[f126,f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f20])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.55  fof(f126,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~v1_relat_1(sK3) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3))) )),
% 1.34/0.55    inference(resolution,[],[f75,f47])).
% 1.34/0.55  fof(f47,plain,(
% 1.34/0.55    v1_funct_1(sK3)),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f75,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 1.34/0.55    inference(flattening,[],[f28])).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 1.34/0.55    inference(ennf_transformation,[],[f11])).
% 1.34/0.55  fof(f11,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 1.34/0.55  fof(f101,plain,(
% 1.34/0.55    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.34/0.55    inference(equality_resolution,[],[f100])).
% 1.34/0.55  fof(f100,plain,(
% 1.34/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.34/0.55    inference(equality_resolution,[],[f90])).
% 1.34/0.55  fof(f90,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.34/0.55    inference(definition_unfolding,[],[f61,f85])).
% 1.34/0.55  fof(f61,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f40])).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (2535)------------------------------
% 1.34/0.55  % (2535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (2535)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (2535)Memory used [KB]: 6396
% 1.34/0.55  % (2535)Time elapsed: 0.092 s
% 1.34/0.55  % (2535)------------------------------
% 1.34/0.55  % (2535)------------------------------
% 1.43/0.55  % (2512)Success in time 0.185 s
%------------------------------------------------------------------------------

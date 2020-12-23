%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 950 expanded)
%              Number of leaves         :   12 ( 319 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 (4710 expanded)
%              Number of equality atoms :   99 ( 589 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f169])).

fof(f169,plain,(
    ! [X3] : r2_hidden(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f74,f164])).

fof(f164,plain,(
    ! [X1] : k1_xboole_0 = X1 ),
    inference(subsumption_resolution,[],[f162,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f162,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f68,f133])).

fof(f133,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f129,f113])).

fof(f113,plain,
    ( sK1 = k1_funct_1(sK2,sK5(sK0,sK2,sK3))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f111,f88])).

fof(f88,plain,(
    r2_hidden(sK5(sK0,sK2,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f39,f66,f64,f62,f63,f65,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | r2_hidden(sK5(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
            & r2_hidden(sK5(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f33])).

fof(f33,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & r2_hidden(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK2,sK0,k1_tarski(sK1))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK2,sK0,k1_tarski(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ~ r2_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f42,plain,(
    ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    v1_funct_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK1 = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f110,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f110,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k1_enumset1(sK1,sK1,sK1))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f106,f66])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))
      | r2_hidden(k1_funct_1(sK2,X0),k1_enumset1(sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X2,X0)
      | r2_hidden(k1_funct_1(sK2,X1),X0) ) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

% (31392)Refutation not found, incomplete strategy% (31392)------------------------------
% (31392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f129,plain,
    ( sK1 != k1_funct_1(sK2,sK5(sK0,sK2,sK3))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(superposition,[],[f89,f128])).

fof(f128,plain,
    ( sK1 = k1_funct_1(sK3,sK5(sK0,sK2,sK3))
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(resolution,[],[f121,f88])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | sK1 = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f118,f75])).

fof(f118,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
      | ~ v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
      | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f82,f63])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X2,X0)
      | r2_hidden(k1_funct_1(sK3,X1),X0) ) ),
    inference(resolution,[],[f39,f58])).

fof(f89,plain,(
    k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != k1_funct_1(sK3,sK5(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f36,f39,f66,f64,f62,f63,f65,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f171,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK3)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f95,f164])).

fof(f95,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK3)),k1_enumset1(k1_funct_1(sK3,sK5(sK0,sK2,sK3)),k1_funct_1(sK3,sK5(sK0,sK2,sK3)),k1_funct_1(sK3,sK5(sK0,sK2,sK3)))) ),
    inference(unit_resulting_resolution,[],[f89,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (31379)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (31384)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (31384)Refutation not found, incomplete strategy% (31384)------------------------------
% 0.20/0.54  % (31384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31379)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (31392)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (31384)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31384)Memory used [KB]: 10746
% 0.20/0.55  % (31384)Time elapsed: 0.116 s
% 0.20/0.55  % (31384)------------------------------
% 0.20/0.55  % (31384)------------------------------
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f171,f169])).
% 0.20/0.55  fof(f169,plain,(
% 0.20/0.55    ( ! [X3] : (r2_hidden(X3,k1_xboole_0)) )),
% 0.20/0.55    inference(backward_demodulation,[],[f74,f164])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = X1) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f162,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.55    inference(superposition,[],[f68,f133])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f129,f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    sK1 = k1_funct_1(sK2,sK5(sK0,sK2,sK3)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.55    inference(resolution,[],[f111,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    r2_hidden(sK5(sK0,sK2,sK3),sK0)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f36,f39,f66,f64,f62,f63,f65,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | r2_hidden(sK5(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | (k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) & r2_hidden(sK5(X0,X2,X3),X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) & r2_hidden(sK5(X0,X2,X3),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 0.20/0.55    inference(definition_unfolding,[],[f38,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f44,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    (~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK2,sK0,k1_tarski(sK1)) & v1_funct_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f25,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,k1_tarski(sK1),sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK2,sK0,k1_tarski(sK1)) & v1_funct_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ? [X3] : (~r2_relset_1(sK0,k1_tarski(sK1),sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.20/0.55    inference(negated_conjecture,[],[f11])).
% 0.20/0.55  fof(f11,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 0.20/0.55    inference(definition_unfolding,[],[f41,f61])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,k1_enumset1(sK1,sK1,sK1),sK2,sK3)),
% 0.20/0.55    inference(definition_unfolding,[],[f42,f61])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f40,f61])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f37,f61])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK1 = k1_funct_1(sK2,X0)) )),
% 0.20/0.55    inference(resolution,[],[f110,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.20/0.55    inference(definition_unfolding,[],[f48,f61])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f106,f66])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_2(sK2,sK0,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(k1_funct_1(sK2,X0),k1_enumset1(sK1,sK1,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f80,f65])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X2,X0) | r2_hidden(k1_funct_1(sK2,X1),X0)) )),
% 0.20/0.55    inference(resolution,[],[f36,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  % (31392)Refutation not found, incomplete strategy% (31392)------------------------------
% 0.20/0.55  % (31392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    sK1 != k1_funct_1(sK2,sK5(sK0,sK2,sK3)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.55    inference(superposition,[],[f89,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    sK1 = k1_funct_1(sK3,sK5(sK0,sK2,sK3)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.20/0.55    inference(resolution,[],[f121,f88])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | sK1 = k1_funct_1(sK3,X0)) )),
% 0.20/0.55    inference(resolution,[],[f118,f75])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f114,f64])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(k1_funct_1(sK3,X0),k1_enumset1(sK1,sK1,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f82,f63])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X2,X0) | r2_hidden(k1_funct_1(sK3,X1),X0)) )),
% 0.20/0.55    inference(resolution,[],[f39,f58])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    k1_funct_1(sK2,sK5(sK0,sK2,sK3)) != k1_funct_1(sK3,sK5(sK0,sK2,sK3))),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f36,f39,f66,f64,f62,f63,f65,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) | r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f46,f61])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.20/0.56    inference(equality_resolution,[],[f73])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.20/0.56    inference(equality_resolution,[],[f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.20/0.56    inference(definition_unfolding,[],[f49,f61])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    ~r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK3)),k1_xboole_0)),
% 0.20/0.56    inference(backward_demodulation,[],[f95,f164])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    ~r2_hidden(k1_funct_1(sK2,sK5(sK0,sK2,sK3)),k1_enumset1(k1_funct_1(sK3,sK5(sK0,sK2,sK3)),k1_funct_1(sK3,sK5(sK0,sK2,sK3)),k1_funct_1(sK3,sK5(sK0,sK2,sK3))))),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f89,f75])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (31379)------------------------------
% 0.20/0.56  % (31379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31379)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (31379)Memory used [KB]: 6396
% 0.20/0.56  % (31379)Time elapsed: 0.134 s
% 0.20/0.56  % (31379)------------------------------
% 0.20/0.56  % (31379)------------------------------
% 0.20/0.56  % (31392)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31392)Memory used [KB]: 10618
% 0.20/0.56  % (31392)Time elapsed: 0.136 s
% 0.20/0.56  % (31392)------------------------------
% 0.20/0.56  % (31392)------------------------------
% 0.20/0.56  % (31367)Success in time 0.2 s
%------------------------------------------------------------------------------

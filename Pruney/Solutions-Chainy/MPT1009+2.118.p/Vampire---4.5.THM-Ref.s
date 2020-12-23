%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:43 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 544 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   37
%              Number of atoms          :  353 (1434 expanded)
%              Number of equality atoms :  159 ( 569 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f490,plain,(
    $false ),
    inference(resolution,[],[f479,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f479,plain,(
    ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f122,f468])).

fof(f468,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f457,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f457,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
      | k1_xboole_0 = k9_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f447,f79])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f45,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f31])).

% (19007)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f31,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
      | k1_xboole_0 = k9_relat_1(sK3,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f439,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f439,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k1_xboole_0 = k9_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f437,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

% (19017)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f437,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f65,f425])).

fof(f425,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f420,f61])).

fof(f420,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(resolution,[],[f409,f79])).

fof(f409,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | k1_xboole_0 = k2_relat_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f408,f60])).

fof(f408,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f396])).

fof(f396,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f58,f386])).

fof(f386,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f384,f61])).

fof(f384,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f380,f253])).

fof(f253,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f79,f243])).

fof(f243,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f241,f61])).

fof(f241,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f240,f79])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f148,f60])).

fof(f148,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(resolution,[],[f144,f79])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)))
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(resolution,[],[f128,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ v4_relat_1(X2,k2_enumset1(X3,X3,X3,X3))
      | k1_relat_1(X2) = k2_enumset1(X3,X3,X3,X3)
      | k1_xboole_0 = k1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f77,f77])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f380,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f378,f60])).

fof(f378,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f376,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f376,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3)))
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f340,f243])).

fof(f340,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f122,f335])).

fof(f335,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f333,f61])).

fof(f333,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(resolution,[],[f329,f253])).

fof(f329,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 = k1_relat_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f327,f60])).

fof(f327,plain,
    ( ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f276,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f276,plain,
    ( ~ v1_funct_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f255,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k9_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(factoring,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f56,f76,f76])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f255,plain,
    ( r2_hidden(sK0,k1_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(superposition,[],[f96,f243])).

fof(f96,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f88])).

% (19026)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f122,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f78,f121])).

fof(f121,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f57,f79])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f78,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f47,f77,f77])).

fof(f47,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:33:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (19015)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (19031)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.22/0.52  % (19008)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (19031)Refutation not found, incomplete strategy% (19031)------------------------------
% 1.36/0.54  % (19031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19031)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19031)Memory used [KB]: 6268
% 1.36/0.54  % (19031)Time elapsed: 0.122 s
% 1.36/0.54  % (19031)------------------------------
% 1.36/0.54  % (19031)------------------------------
% 1.36/0.57  % (19011)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.57  % (19009)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.57  % (19032)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.57  % (19004)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.57  % (19004)Refutation not found, incomplete strategy% (19004)------------------------------
% 1.36/0.57  % (19004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (19004)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (19004)Memory used [KB]: 1663
% 1.36/0.57  % (19004)Time elapsed: 0.140 s
% 1.36/0.57  % (19004)------------------------------
% 1.36/0.57  % (19004)------------------------------
% 1.36/0.58  % (19016)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.58  % (19019)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.58  % (19019)Refutation not found, incomplete strategy% (19019)------------------------------
% 1.36/0.58  % (19019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (19019)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (19019)Memory used [KB]: 10618
% 1.36/0.58  % (19019)Time elapsed: 0.147 s
% 1.36/0.58  % (19019)------------------------------
% 1.36/0.58  % (19019)------------------------------
% 1.36/0.58  % (19025)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.59  % (19024)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.59  % (19018)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.59  % (19027)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.59  % (19008)Refutation found. Thanks to Tanya!
% 1.36/0.59  % SZS status Theorem for theBenchmark
% 1.36/0.59  % SZS output start Proof for theBenchmark
% 1.36/0.59  fof(f490,plain,(
% 1.36/0.59    $false),
% 1.36/0.59    inference(resolution,[],[f479,f55])).
% 1.36/0.59  fof(f55,plain,(
% 1.36/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f2])).
% 1.36/0.59  fof(f2,axiom,(
% 1.36/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.59  fof(f479,plain,(
% 1.36/0.59    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.36/0.59    inference(backward_demodulation,[],[f122,f468])).
% 1.36/0.59  fof(f468,plain,(
% 1.36/0.59    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.36/0.59    inference(resolution,[],[f457,f61])).
% 1.36/0.59  fof(f61,plain,(
% 1.36/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f10])).
% 1.36/0.59  fof(f10,axiom,(
% 1.36/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.59  fof(f457,plain,(
% 1.36/0.59    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.36/0.59    inference(resolution,[],[f447,f79])).
% 1.36/0.59  fof(f79,plain,(
% 1.36/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.36/0.59    inference(definition_unfolding,[],[f45,f77])).
% 1.36/0.59  fof(f77,plain,(
% 1.36/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.36/0.59    inference(definition_unfolding,[],[f62,f76])).
% 1.36/0.59  fof(f76,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.59    inference(definition_unfolding,[],[f72,f75])).
% 1.36/0.59  fof(f75,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f6])).
% 1.36/0.59  fof(f6,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.59  fof(f72,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f5])).
% 1.36/0.59  fof(f5,axiom,(
% 1.36/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.59  fof(f62,plain,(
% 1.36/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f4])).
% 1.36/0.59  fof(f4,axiom,(
% 1.36/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.59  fof(f45,plain,(
% 1.36/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.36/0.59    inference(cnf_transformation,[],[f31])).
% 1.36/0.59  % (19007)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.59  fof(f31,plain,(
% 1.36/0.59    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f30])).
% 1.36/0.59  fof(f30,plain,(
% 1.36/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f20,plain,(
% 1.36/0.59    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.36/0.59    inference(flattening,[],[f19])).
% 1.36/0.59  fof(f19,plain,(
% 1.36/0.59    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.36/0.59    inference(ennf_transformation,[],[f18])).
% 1.36/0.59  fof(f18,negated_conjecture,(
% 1.36/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.59    inference(negated_conjecture,[],[f17])).
% 1.36/0.59  fof(f17,conjecture,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.36/0.59  fof(f447,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X1)) | k1_xboole_0 = k9_relat_1(sK3,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.59    inference(resolution,[],[f439,f60])).
% 1.36/0.59  fof(f60,plain,(
% 1.36/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f26])).
% 1.36/0.59  fof(f26,plain,(
% 1.36/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.59    inference(ennf_transformation,[],[f8])).
% 1.36/0.59  fof(f8,axiom,(
% 1.36/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.59  fof(f439,plain,(
% 1.36/0.59    ( ! [X0] : (~v1_relat_1(sK3) | k1_xboole_0 = k9_relat_1(sK3,X0)) )),
% 1.36/0.59    inference(resolution,[],[f437,f102])).
% 1.36/0.59  fof(f102,plain,(
% 1.36/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.36/0.59    inference(resolution,[],[f53,f55])).
% 1.36/0.59  fof(f53,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.36/0.59    inference(cnf_transformation,[],[f35])).
% 1.36/0.60  fof(f35,plain,(
% 1.36/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.60    inference(flattening,[],[f34])).
% 1.36/0.60  fof(f34,plain,(
% 1.36/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.60    inference(nnf_transformation,[],[f1])).
% 1.36/0.60  fof(f1,axiom,(
% 1.36/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.60  % (19017)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.60  fof(f437,plain,(
% 1.36/0.60    ( ! [X1] : (r1_tarski(k9_relat_1(sK3,X1),k1_xboole_0) | ~v1_relat_1(sK3)) )),
% 1.36/0.60    inference(superposition,[],[f65,f425])).
% 1.36/0.60  fof(f425,plain,(
% 1.36/0.60    k1_xboole_0 = k2_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f420,f61])).
% 1.36/0.60  fof(f420,plain,(
% 1.36/0.60    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f409,f79])).
% 1.36/0.60  fof(f409,plain,(
% 1.36/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(X0)) )),
% 1.36/0.60    inference(resolution,[],[f408,f60])).
% 1.36/0.60  fof(f408,plain,(
% 1.36/0.60    ~v1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 1.36/0.60    inference(trivial_inequality_removal,[],[f396])).
% 1.36/0.60  fof(f396,plain,(
% 1.36/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.36/0.60    inference(superposition,[],[f58,f386])).
% 1.36/0.60  fof(f386,plain,(
% 1.36/0.60    k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f384,f61])).
% 1.36/0.60  fof(f384,plain,(
% 1.36/0.60    ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(duplicate_literal_removal,[],[f383])).
% 1.36/0.60  fof(f383,plain,(
% 1.36/0.60    k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f380,f253])).
% 1.36/0.60  fof(f253,plain,(
% 1.36/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(superposition,[],[f79,f243])).
% 1.36/0.60  fof(f243,plain,(
% 1.36/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f241,f61])).
% 1.36/0.60  fof(f241,plain,(
% 1.36/0.60    ~v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f240,f79])).
% 1.36/0.60  fof(f240,plain,(
% 1.36/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(X0)) )),
% 1.36/0.60    inference(resolution,[],[f148,f60])).
% 1.36/0.60  fof(f148,plain,(
% 1.36/0.60    ~v1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f144,f79])).
% 1.36/0.60  fof(f144,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_enumset1(X1,X1,X1,X1)) )),
% 1.36/0.60    inference(resolution,[],[f128,f73])).
% 1.36/0.60  fof(f73,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.60    inference(cnf_transformation,[],[f29])).
% 1.36/0.60  fof(f29,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.60    inference(ennf_transformation,[],[f15])).
% 1.36/0.60  fof(f15,axiom,(
% 1.36/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.60  fof(f128,plain,(
% 1.36/0.60    ( ! [X2,X3] : (~v4_relat_1(X2,k2_enumset1(X3,X3,X3,X3)) | k1_relat_1(X2) = k2_enumset1(X3,X3,X3,X3) | k1_xboole_0 = k1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 1.36/0.60    inference(resolution,[],[f83,f63])).
% 1.36/0.60  fof(f63,plain,(
% 1.36/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f37])).
% 1.36/0.60  fof(f37,plain,(
% 1.36/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.36/0.60    inference(nnf_transformation,[],[f27])).
% 1.36/0.60  fof(f27,plain,(
% 1.36/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.60    inference(ennf_transformation,[],[f9])).
% 1.36/0.60  fof(f9,axiom,(
% 1.36/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.36/0.60  fof(f83,plain,(
% 1.36/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.36/0.60    inference(definition_unfolding,[],[f48,f77,f77])).
% 1.36/0.60  fof(f48,plain,(
% 1.36/0.60    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.36/0.60    inference(cnf_transformation,[],[f33])).
% 1.36/0.60  fof(f33,plain,(
% 1.36/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.36/0.60    inference(flattening,[],[f32])).
% 1.36/0.60  fof(f32,plain,(
% 1.36/0.60    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.36/0.60    inference(nnf_transformation,[],[f7])).
% 1.36/0.60  fof(f7,axiom,(
% 1.36/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.36/0.60  fof(f380,plain,(
% 1.36/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(X0)) )),
% 1.36/0.60    inference(resolution,[],[f378,f60])).
% 1.36/0.60  fof(f378,plain,(
% 1.36/0.60    ~v1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f376,f54])).
% 1.36/0.60  fof(f54,plain,(
% 1.36/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f21])).
% 1.36/0.60  fof(f21,plain,(
% 1.36/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.36/0.60    inference(ennf_transformation,[],[f12])).
% 1.36/0.60  fof(f12,axiom,(
% 1.36/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).
% 1.36/0.60  fof(f376,plain,(
% 1.36/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(duplicate_literal_removal,[],[f372])).
% 1.36/0.60  fof(f372,plain,(
% 1.36/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k1_relat_1(sK3))) | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(superposition,[],[f340,f243])).
% 1.36/0.60  fof(f340,plain,(
% 1.36/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(superposition,[],[f122,f335])).
% 1.36/0.60  fof(f335,plain,(
% 1.36/0.60    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f333,f61])).
% 1.36/0.60  fof(f333,plain,(
% 1.36/0.60    ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.36/0.60    inference(duplicate_literal_removal,[],[f332])).
% 1.36/0.60  fof(f332,plain,(
% 1.36/0.60    k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f329,f253])).
% 1.36/0.60  fof(f329,plain,(
% 1.36/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(X0)) )),
% 1.36/0.60    inference(resolution,[],[f327,f60])).
% 1.36/0.60  fof(f327,plain,(
% 1.36/0.60    ~v1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.36/0.60    inference(resolution,[],[f276,f43])).
% 1.36/0.60  fof(f43,plain,(
% 1.36/0.60    v1_funct_1(sK3)),
% 1.36/0.60    inference(cnf_transformation,[],[f31])).
% 1.36/0.60  fof(f276,plain,(
% 1.36/0.60    ~v1_funct_1(sK3) | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.36/0.60    inference(resolution,[],[f255,f143])).
% 1.36/0.60  fof(f143,plain,(
% 1.36/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k9_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.60    inference(factoring,[],[f84])).
% 1.36/0.60  fof(f84,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.36/0.60    inference(definition_unfolding,[],[f56,f76,f76])).
% 1.36/0.60  fof(f56,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f23])).
% 1.36/0.60  fof(f23,plain,(
% 1.36/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.36/0.60    inference(flattening,[],[f22])).
% 1.36/0.60  fof(f22,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.36/0.60    inference(ennf_transformation,[],[f14])).
% 1.36/0.60  fof(f14,axiom,(
% 1.36/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 1.36/0.60  fof(f255,plain,(
% 1.36/0.60    r2_hidden(sK0,k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.36/0.60    inference(superposition,[],[f96,f243])).
% 1.36/0.60  fof(f96,plain,(
% 1.36/0.60    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 1.36/0.60    inference(equality_resolution,[],[f95])).
% 1.36/0.60  fof(f95,plain,(
% 1.36/0.60    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 1.36/0.60    inference(equality_resolution,[],[f88])).
% 1.36/0.60  % (19026)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.60  fof(f88,plain,(
% 1.36/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.36/0.60    inference(definition_unfolding,[],[f68,f76])).
% 1.36/0.60  fof(f68,plain,(
% 1.36/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.36/0.60    inference(cnf_transformation,[],[f42])).
% 1.36/0.60  fof(f42,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.36/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.36/0.60  fof(f41,plain,(
% 1.36/0.60    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.36/0.60    introduced(choice_axiom,[])).
% 1.36/0.60  fof(f40,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.36/0.60    inference(rectify,[],[f39])).
% 1.36/0.60  fof(f39,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.36/0.60    inference(flattening,[],[f38])).
% 1.36/0.60  fof(f38,plain,(
% 1.36/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.36/0.60    inference(nnf_transformation,[],[f3])).
% 1.36/0.60  fof(f3,axiom,(
% 1.36/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.36/0.60  fof(f58,plain,(
% 1.36/0.60    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f36])).
% 1.36/0.60  fof(f36,plain,(
% 1.36/0.60    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.60    inference(nnf_transformation,[],[f25])).
% 1.36/0.60  fof(f25,plain,(
% 1.36/0.60    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.60    inference(ennf_transformation,[],[f13])).
% 1.36/0.60  fof(f13,axiom,(
% 1.36/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.36/0.60  fof(f65,plain,(
% 1.36/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f28])).
% 1.36/0.60  fof(f28,plain,(
% 1.36/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.60    inference(ennf_transformation,[],[f11])).
% 1.36/0.60  fof(f11,axiom,(
% 1.36/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.36/0.60  fof(f122,plain,(
% 1.36/0.60    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.36/0.60    inference(backward_demodulation,[],[f78,f121])).
% 1.36/0.60  fof(f121,plain,(
% 1.36/0.60    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.36/0.60    inference(resolution,[],[f57,f79])).
% 1.36/0.60  fof(f57,plain,(
% 1.36/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f24])).
% 1.36/0.60  fof(f24,plain,(
% 1.36/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.60    inference(ennf_transformation,[],[f16])).
% 1.36/0.60  fof(f16,axiom,(
% 1.36/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.36/0.60  fof(f78,plain,(
% 1.36/0.60    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.36/0.60    inference(definition_unfolding,[],[f47,f77,f77])).
% 1.36/0.60  fof(f47,plain,(
% 1.36/0.60    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.36/0.60    inference(cnf_transformation,[],[f31])).
% 1.36/0.60  % SZS output end Proof for theBenchmark
% 1.36/0.60  % (19008)------------------------------
% 1.36/0.60  % (19008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.60  % (19008)Termination reason: Refutation
% 1.36/0.60  
% 1.36/0.60  % (19008)Memory used [KB]: 2046
% 1.36/0.60  % (19008)Time elapsed: 0.188 s
% 1.36/0.60  % (19008)------------------------------
% 1.36/0.60  % (19008)------------------------------
% 1.36/0.60  % (18999)Success in time 0.237 s
%------------------------------------------------------------------------------

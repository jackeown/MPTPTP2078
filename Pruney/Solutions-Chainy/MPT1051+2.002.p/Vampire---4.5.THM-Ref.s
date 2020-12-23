%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 201 expanded)
%              Number of leaves         :   10 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (1221 expanded)
%              Number of equality atoms :   40 ( 331 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f105])).

fof(f105,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f93,f40])).

fof(f40,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
    & ! [X4] : k1_tarski(X4) != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
            & ! [X4] : k1_tarski(X4) != X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3)
          & ! [X4] : k1_tarski(X4) != sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3)
        & ! [X4] : k1_tarski(X4) != sK1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)
      & ! [X4] : k1_tarski(X4) != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_2)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f93,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f28,f81])).

fof(f81,plain,
    ( sK2 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f28,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,
    ( spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f89,f75,f79])).

fof(f75,plain,
    ( spl5_1
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f89,plain,
    ( sK2 = sK3
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f88,f65])).

fof(f65,plain,(
    r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_relset_1(sK0,sK1,sK2,X0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f33,f23])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_relset_1(X0,X1,X2,X3)
      | r1_tarski(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_relset_1(X0,X1,X2,X3)
          | ~ r1_tarski(X2,X3) )
        & ( r1_tarski(X2,X3)
          | ~ r1_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(f61,plain,(
    r1_relset_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f60,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f58,f23])).

fof(f58,plain,
    ( r1_relset_1(sK0,sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X4] : k1_tarski(X4) != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f32,f27])).

fof(f27,plain,(
    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | k1_tarski(sK4(X1)) = X1
      | r1_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | k1_tarski(sK4(X1)) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ? [X4] : k1_tarski(X4) = X1
     => k1_tarski(sK4(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_2)).

fof(f88,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK2,sK3)
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f87,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f84,f75])).

fof(f84,plain,(
    r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ r1_relset_1(sK0,sK1,sK3,X1)
      | r1_tarski(sK3,X1) ) ),
    inference(resolution,[],[f33,f25])).

fof(f69,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f68,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f66,f23])).

fof(f66,plain,
    ( r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f57,f36])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f50,f26])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,sK3,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f32,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (31267)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (31270)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (31269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (31288)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (31283)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (31286)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (31285)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (31268)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (31284)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (31274)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (31270)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f87,f90,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~spl5_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    $false | ~spl5_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f93,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.50    inference(resolution,[],[f38,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    (~r2_relset_1(sK0,sK1,sK2,sK3) & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) & ! [X4] : k1_tarski(X4) != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3) & ! [X4] : k1_tarski(X4) != sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,X3) & ! [X4] : k1_tarski(X4) != sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) & ! [X4] : k1_tarski(X4) != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & (k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_2)).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.20/0.50    inference(condensation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl5_2),
% 0.20/0.50    inference(backward_demodulation,[],[f28,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    sK2 = sK3 | ~spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl5_2 <=> sK2 = sK3),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl5_2 | ~spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f89,f75,f79])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl5_1 <=> r1_tarski(sK3,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    sK2 = sK3 | ~spl5_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f88,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    r1_tarski(sK2,sK3)),
% 0.20/0.50    inference(resolution,[],[f61,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_relset_1(sK0,sK1,sK2,X0) | r1_tarski(sK2,X0)) )),
% 0.20/0.50    inference(resolution,[],[f33,f23])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_relset_1(X0,X1,X2,X3) | r1_tarski(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (((r1_relset_1(X0,X1,X2,X3) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r1_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r1_relset_1(X0,X1,X2,X3) <=> r1_tarski(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_relset_1(X0,X1,X2,X3) <=> r1_tarski(X2,X3)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_relset_1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK2,sK3) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f58,f23])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f54,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0)) | r1_relset_1(sK0,sK1,X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f53,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0)) | r1_relset_1(sK0,sK1,X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_1(sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f52,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0)) | r1_relset_1(sK0,sK1,X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f49,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X4] : (k1_tarski(X4) != sK1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.50    inference(superposition,[],[f32,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) | k1_tarski(sK4(X1)) = X1 | r1_relset_1(X0,X1,X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (r1_relset_1(X0,X1,X3,X2) | k1_tarski(sK4(X1)) = X1 | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X1] : (? [X4] : k1_tarski(X4) = X1 => k1_tarski(sK4(X1)) = X1)),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : (r1_relset_1(X0,X1,X3,X2) | ? [X4] : k1_tarski(X4) = X1 | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (! [X3] : ((r1_relset_1(X0,X1,X3,X2) | (? [X4] : k1_tarski(X4) = X1 | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((! [X4] : k1_tarski(X4) != X1 & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))) => r1_relset_1(X0,X1,X3,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_2)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    sK2 = sK3 | ~r1_tarski(sK2,sK3) | ~spl5_1),
% 0.20/0.50    inference(resolution,[],[f76,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2) | ~spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f84,f75])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    r1_tarski(sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f69,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_relset_1(sK0,sK1,sK3,X1) | r1_tarski(sK3,X1)) )),
% 0.20/0.50    inference(resolution,[],[f33,f25])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f22])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK3,sK2) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f23])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    r1_relset_1(sK0,sK1,sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f57,f36])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f56,f24])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f55,f25])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f50,f26])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k5_partfun1(sK0,sK1,X0),k5_partfun1(sK0,sK1,sK2)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(superposition,[],[f32,f27])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31270)------------------------------
% 0.20/0.50  % (31270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31270)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31270)Memory used [KB]: 6140
% 0.20/0.50  % (31270)Time elapsed: 0.092 s
% 0.20/0.50  % (31270)------------------------------
% 0.20/0.50  % (31270)------------------------------
% 0.20/0.50  % (31265)Success in time 0.146 s
%------------------------------------------------------------------------------

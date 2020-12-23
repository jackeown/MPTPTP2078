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
% DateTime   : Thu Dec  3 13:06:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 687 expanded)
%              Number of leaves         :   15 ( 219 expanded)
%              Depth                    :   22
%              Number of atoms          :  311 (5590 expanded)
%              Number of equality atoms :   66 (1131 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(resolution,[],[f305,f99])).

fof(f99,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f66,f79])).

fof(f79,plain,(
    ! [X0,X1] : ~ sP7(X0,X1) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f61,f66_D])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f66_D])).

fof(f66_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f305,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f272,f294])).

fof(f294,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f293,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f293,plain,(
    ! [X0] : ~ r2_hidden(X0,sK3) ),
    inference(resolution,[],[f291,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP6(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f60,f64_D])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f64_D])).

fof(f64_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f291,plain,(
    sP6(sK3) ),
    inference(resolution,[],[f248,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | sP6(X0) ) ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f248,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f220,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

% (24354)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f220,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f42,f215])).

fof(f215,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f100,f207])).

fof(f207,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f45,f202])).

fof(f202,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f200,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f200,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(global_subsumption,[],[f43,f37,f144,f195])).

fof(f195,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f193,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_partfun1(X0,sK3)
      | sK3 = X0
      | ~ v1_partfun1(X0,sK0)
      | ~ v1_funct_1(X0)
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f190,f148])).

fof(f148,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f41,f145])).

fof(f145,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f140,f42])).

fof(f140,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_partfun1(sK3,X2)
      | ~ v1_funct_2(sK3,X2,X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f190,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X0,sK0)
      | ~ r1_partfun1(X0,sK3)
      | sK3 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f178,f42])).

fof(f178,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_partfun1(sK3,X4)
      | ~ v1_partfun1(X3,X4)
      | ~ r1_partfun1(X3,sK3)
      | sK3 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

% (24358)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f144,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f38,f141])).

fof(f141,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f139,f39])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK2,X0)
      | ~ v1_funct_2(sK2,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f54,f37])).

fof(f38,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f85,f39])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f272,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f251,f263])).

fof(f263,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f262,f49])).

fof(f262,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(resolution,[],[f260,f65])).

fof(f260,plain,(
    sP6(sK2) ),
    inference(resolution,[],[f244,f69])).

fof(f244,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f218,f62])).

fof(f218,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f39,f215])).

fof(f251,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3) ),
    inference(forward_demodulation,[],[f221,f216])).

fof(f216,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f44,f215])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f221,plain,(
    ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    inference(backward_demodulation,[],[f45,f215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (24339)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (24360)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (24349)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (24352)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (24342)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (24341)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24362)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (24347)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (24344)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (24349)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (24344)Refutation not found, incomplete strategy% (24344)------------------------------
% 0.21/0.52  % (24344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24344)Memory used [KB]: 1663
% 0.21/0.52  % (24344)Time elapsed: 0.071 s
% 0.21/0.52  % (24344)------------------------------
% 0.21/0.52  % (24344)------------------------------
% 0.21/0.52  % (24356)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (24343)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (24346)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (24343)Refutation not found, incomplete strategy% (24343)------------------------------
% 0.21/0.52  % (24343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24343)Memory used [KB]: 10618
% 0.21/0.52  % (24343)Time elapsed: 0.117 s
% 0.21/0.52  % (24343)------------------------------
% 0.21/0.52  % (24343)------------------------------
% 0.21/0.52  % (24359)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (24361)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f318,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(resolution,[],[f305,f99])).
% 1.31/0.53  fof(f99,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 1.31/0.53    inference(resolution,[],[f85,f47])).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.31/0.53  fof(f85,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 1.31/0.53    inference(subsumption_resolution,[],[f66,f79])).
% 1.31/0.53  fof(f79,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP7(X0,X1)) )),
% 1.31/0.53    inference(resolution,[],[f67,f47])).
% 1.31/0.53  fof(f67,plain,(
% 1.31/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP7(X1,X0)) )),
% 1.31/0.53    inference(general_splitting,[],[f61,f66_D])).
% 1.31/0.53  fof(f61,plain,(
% 1.31/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.31/0.53    inference(flattening,[],[f26])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.31/0.53  fof(f66,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP7(X1,X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f66_D])).
% 1.31/0.53  fof(f66_D,plain,(
% 1.31/0.53    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP7(X1,X0)) )),
% 1.31/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.31/0.53  fof(f305,plain,(
% 1.31/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.31/0.53    inference(backward_demodulation,[],[f272,f294])).
% 1.31/0.53  fof(f294,plain,(
% 1.31/0.53    k1_xboole_0 = sK3),
% 1.31/0.53    inference(resolution,[],[f293,f49])).
% 1.31/0.53  fof(f49,plain,(
% 1.31/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f31])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.31/0.53    inference(ennf_transformation,[],[f9])).
% 1.31/0.53  fof(f9,axiom,(
% 1.31/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.31/0.53  fof(f293,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(X0,sK3)) )),
% 1.31/0.53    inference(resolution,[],[f291,f65])).
% 1.31/0.53  fof(f65,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~sP6(X1) | ~r2_hidden(X0,X1)) )),
% 1.31/0.53    inference(general_splitting,[],[f60,f64_D])).
% 1.31/0.53  fof(f64,plain,(
% 1.31/0.53    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP6(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f64_D])).
% 1.31/0.53  fof(f64_D,plain,(
% 1.31/0.53    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP6(X1)) )),
% 1.31/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.31/0.53  fof(f60,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f25])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f7])).
% 1.31/0.53  fof(f7,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.31/0.53  fof(f291,plain,(
% 1.31/0.53    sP6(sK3)),
% 1.31/0.53    inference(resolution,[],[f248,f69])).
% 1.31/0.53  fof(f69,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP6(X0)) )),
% 1.31/0.53    inference(resolution,[],[f64,f46])).
% 1.31/0.53  fof(f46,plain,(
% 1.31/0.53    v1_xboole_0(k1_xboole_0)),
% 1.31/0.53    inference(cnf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    v1_xboole_0(k1_xboole_0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.31/0.53  fof(f248,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.31/0.53    inference(forward_demodulation,[],[f220,f62])).
% 1.31/0.53  fof(f62,plain,(
% 1.31/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.31/0.53    inference(equality_resolution,[],[f57])).
% 1.31/0.53  fof(f57,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.31/0.53    inference(flattening,[],[f35])).
% 1.31/0.53  fof(f35,plain,(
% 1.31/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.31/0.53    inference(nnf_transformation,[],[f3])).
% 1.31/0.53  % (24354)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.31/0.53  fof(f220,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.31/0.53    inference(backward_demodulation,[],[f42,f215])).
% 1.31/0.53  fof(f215,plain,(
% 1.31/0.53    k1_xboole_0 = sK1),
% 1.31/0.53    inference(global_subsumption,[],[f100,f207])).
% 1.31/0.53  fof(f207,plain,(
% 1.31/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | k1_xboole_0 = sK1),
% 1.31/0.53    inference(superposition,[],[f45,f202])).
% 1.31/0.53  fof(f202,plain,(
% 1.31/0.53    sK2 = sK3 | k1_xboole_0 = sK1),
% 1.31/0.53    inference(resolution,[],[f200,f48])).
% 1.31/0.53  fof(f48,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.31/0.53    inference(cnf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.31/0.53  fof(f200,plain,(
% 1.31/0.53    v1_xboole_0(sK1) | sK2 = sK3),
% 1.31/0.53    inference(global_subsumption,[],[f43,f37,f144,f195])).
% 1.31/0.53  fof(f195,plain,(
% 1.31/0.53    ~r1_partfun1(sK2,sK3) | sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | v1_xboole_0(sK1)),
% 1.31/0.53    inference(resolution,[],[f193,f39])).
% 1.31/0.53  fof(f39,plain,(
% 1.31/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.31/0.53    inference(flattening,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,negated_conjecture,(
% 1.31/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.31/0.53    inference(negated_conjecture,[],[f12])).
% 1.31/0.53  fof(f12,conjecture,(
% 1.31/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 1.31/0.53  fof(f193,plain,(
% 1.31/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0) | v1_xboole_0(sK1)) )),
% 1.31/0.53    inference(resolution,[],[f190,f148])).
% 1.31/0.53  fof(f148,plain,(
% 1.31/0.53    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.31/0.53    inference(global_subsumption,[],[f41,f145])).
% 1.31/0.53  fof(f145,plain,(
% 1.31/0.53    v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,sK1) | v1_xboole_0(sK1)),
% 1.31/0.53    inference(resolution,[],[f140,f42])).
% 1.31/0.53  fof(f140,plain,(
% 1.31/0.53    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_partfun1(sK3,X2) | ~v1_funct_2(sK3,X2,X3) | v1_xboole_0(X3)) )),
% 1.31/0.53    inference(resolution,[],[f54,f40])).
% 1.31/0.53  fof(f40,plain,(
% 1.31/0.53    v1_funct_1(sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f54,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f20])).
% 1.31/0.53  fof(f20,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.31/0.53    inference(flattening,[],[f19])).
% 1.31/0.53  fof(f19,plain,(
% 1.31/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f190,plain,(
% 1.31/0.53    ( ! [X0] : (~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | ~r1_partfun1(X0,sK3) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 1.31/0.53    inference(resolution,[],[f178,f42])).
% 1.31/0.53  fof(f178,plain,(
% 1.31/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK3,X4) | ~v1_partfun1(X3,X4) | ~r1_partfun1(X3,sK3) | sK3 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3)) )),
% 1.31/0.53    inference(resolution,[],[f58,f40])).
% 1.31/0.53  fof(f58,plain,(
% 1.31/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.31/0.53    inference(flattening,[],[f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.31/0.53    inference(ennf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.31/0.53  % (24358)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.31/0.53  fof(f144,plain,(
% 1.31/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.31/0.53    inference(global_subsumption,[],[f38,f141])).
% 1.31/0.53  fof(f141,plain,(
% 1.31/0.53    v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK1)),
% 1.31/0.53    inference(resolution,[],[f139,f39])).
% 1.31/0.53  fof(f139,plain,(
% 1.31/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1)) )),
% 1.31/0.53    inference(resolution,[],[f54,f37])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    v1_funct_1(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    r1_partfun1(sK2,sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f100,plain,(
% 1.31/0.53    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.31/0.53    inference(resolution,[],[f85,f39])).
% 1.31/0.53  fof(f42,plain,(
% 1.31/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f272,plain,(
% 1.31/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK3)),
% 1.31/0.53    inference(backward_demodulation,[],[f251,f263])).
% 1.31/0.53  fof(f263,plain,(
% 1.31/0.53    k1_xboole_0 = sK2),
% 1.31/0.53    inference(resolution,[],[f262,f49])).
% 1.31/0.53  fof(f262,plain,(
% 1.31/0.53    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 1.31/0.53    inference(resolution,[],[f260,f65])).
% 1.31/0.53  fof(f260,plain,(
% 1.31/0.53    sP6(sK2)),
% 1.31/0.53    inference(resolution,[],[f244,f69])).
% 1.31/0.53  fof(f244,plain,(
% 1.31/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.31/0.53    inference(forward_demodulation,[],[f218,f62])).
% 1.31/0.53  fof(f218,plain,(
% 1.31/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 1.31/0.53    inference(backward_demodulation,[],[f39,f215])).
% 1.31/0.53  fof(f251,plain,(
% 1.31/0.53    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,sK3)),
% 1.31/0.53    inference(forward_demodulation,[],[f221,f216])).
% 1.31/0.53  fof(f216,plain,(
% 1.31/0.53    k1_xboole_0 = sK0),
% 1.31/0.53    inference(subsumption_resolution,[],[f44,f215])).
% 1.31/0.53  fof(f44,plain,(
% 1.31/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.31/0.53    inference(cnf_transformation,[],[f30])).
% 1.31/0.53  fof(f221,plain,(
% 1.31/0.53    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 1.31/0.53    inference(backward_demodulation,[],[f45,f215])).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (24349)------------------------------
% 1.31/0.53  % (24349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (24349)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (24349)Memory used [KB]: 6396
% 1.31/0.53  % (24349)Time elapsed: 0.102 s
% 1.31/0.53  % (24349)------------------------------
% 1.31/0.53  % (24349)------------------------------
% 1.31/0.53  % (24353)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.31/0.53  % (24336)Success in time 0.166 s
%------------------------------------------------------------------------------

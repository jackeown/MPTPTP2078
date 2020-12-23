%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:45 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   94 (1584 expanded)
%              Number of leaves         :   12 ( 470 expanded)
%              Depth                    :   30
%              Number of atoms          :  364 (13016 expanded)
%              Number of equality atoms :   73 (2575 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(subsumption_resolution,[],[f304,f183])).

fof(f183,plain,(
    r2_relset_1(sK0,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f70,f175])).

fof(f175,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f164,f70])).

fof(f164,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f41,f158])).

fof(f158,plain,
    ( sK2 = sK3
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( sK2 = sK3
    | sK2 = sK3
    | sK1 = sK2 ),
    inference(resolution,[],[f143,f113])).

fof(f113,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | sK2 = sK3
      | sK1 = X3 ) ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f109,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f109,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f108,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1)
      | ~ r2_hidden(X0,X1)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | sK2 = sK3
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f105,plain,
    ( v1_xboole_0(sK1)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).

% (4653)Refutation not found, incomplete strategy% (4653)------------------------------
% (4653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4653)Termination reason: Refutation not found, incomplete strategy

% (4653)Memory used [KB]: 10746
% (4653)Time elapsed: 0.124 s
% (4653)------------------------------
% (4653)------------------------------
fof(f22,plain,
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

% (4655)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f23,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f103,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | sK2 = sK3
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f101,f95])).

fof(f95,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f94,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f92,f34])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,X0,X1)
      | v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f101,plain,(
    ! [X0] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK2,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
      | v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f100,f97])).

fof(f97,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f93,f37])).

fof(f37,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(sK3,X2,X3)
      | v1_partfun1(sK3,X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f43,f36])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(sK3,X0)
      | sK2 = sK3
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f99,f33])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f98,f36])).

% (4672)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f98,plain,(
    ! [X0,X1] :
      ( sK2 = sK3
      | ~ v1_partfun1(sK3,X0)
      | ~ v1_partfun1(sK2,X0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f143,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f140,f49])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f139,f57])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2)
      | ~ r2_hidden(X0,X1)
      | sK2 = sK3 ) ),
    inference(resolution,[],[f129,f52])).

fof(f129,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK2))
      | sK2 = sK3
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f125,f54])).

fof(f125,plain,
    ( v1_xboole_0(sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f106,f35])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | sK2 = sK3
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f105,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f41,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f304,plain,(
    ~ r2_relset_1(sK0,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f180,f290])).

fof(f290,plain,(
    sK1 = sK3 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( sK1 = sK3
    | sK1 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f276,f198])).

fof(f198,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | sK1 = sK3
      | sK1 = X3 ) ),
    inference(backward_demodulation,[],[f113,f175])).

fof(f276,plain,(
    ! [X0] :
      ( r1_tarski(sK3,X0)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f272,f49])).

fof(f272,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f271,f57])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK3)
      | ~ r2_hidden(X0,X1)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f206,f52])).

fof(f206,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK3))
      | sK1 = sK3
      | ~ r2_hidden(X3,X2) ) ),
    inference(backward_demodulation,[],[f131,f175])).

fof(f131,plain,(
    ! [X2,X3] :
      ( sK2 = sK3
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK3))
      | ~ r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f126,f54])).

fof(f126,plain,
    ( v1_xboole_0(sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f106,f38])).

fof(f180,plain,(
    ~ r2_relset_1(sK0,sK1,sK1,sK3) ),
    inference(backward_demodulation,[],[f41,f175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (4654)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (4650)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (4647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (4654)Refutation not found, incomplete strategy% (4654)------------------------------
% 0.21/0.50  % (4654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4654)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4654)Memory used [KB]: 10746
% 0.21/0.50  % (4654)Time elapsed: 0.099 s
% 0.21/0.50  % (4654)------------------------------
% 0.21/0.50  % (4654)------------------------------
% 0.21/0.50  % (4671)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (4658)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.51  % (4650)Refutation found. Thanks to Tanya!
% 1.22/0.51  % SZS status Theorem for theBenchmark
% 1.22/0.51  % (4665)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.51  % (4666)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.52  % (4665)Refutation not found, incomplete strategy% (4665)------------------------------
% 1.22/0.52  % (4665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (4665)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (4665)Memory used [KB]: 10746
% 1.22/0.52  % (4665)Time elapsed: 0.080 s
% 1.22/0.52  % (4665)------------------------------
% 1.22/0.52  % (4665)------------------------------
% 1.22/0.52  % (4663)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.53  % (4649)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.53  % (4643)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.53  % (4657)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.53  % (4645)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.53  % (4667)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.53  % (4646)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.53  % (4645)Refutation not found, incomplete strategy% (4645)------------------------------
% 1.39/0.53  % (4645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (4645)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (4645)Memory used [KB]: 10746
% 1.39/0.53  % (4645)Time elapsed: 0.124 s
% 1.39/0.53  % (4645)------------------------------
% 1.39/0.53  % (4645)------------------------------
% 1.39/0.53  % (4648)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.53  % (4644)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.53  % (4653)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f310,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(subsumption_resolution,[],[f304,f183])).
% 1.39/0.53  fof(f183,plain,(
% 1.39/0.53    r2_relset_1(sK0,sK1,sK1,sK1)),
% 1.39/0.53    inference(backward_demodulation,[],[f70,f175])).
% 1.39/0.53  fof(f175,plain,(
% 1.39/0.53    sK1 = sK2),
% 1.39/0.53    inference(subsumption_resolution,[],[f164,f70])).
% 1.39/0.53  fof(f164,plain,(
% 1.39/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | sK1 = sK2),
% 1.39/0.53    inference(superposition,[],[f41,f158])).
% 1.39/0.53  fof(f158,plain,(
% 1.39/0.53    sK2 = sK3 | sK1 = sK2),
% 1.39/0.53    inference(duplicate_literal_removal,[],[f149])).
% 1.39/0.53  fof(f149,plain,(
% 1.39/0.53    sK2 = sK3 | sK2 = sK3 | sK1 = sK2),
% 1.39/0.53    inference(resolution,[],[f143,f113])).
% 1.39/0.53  fof(f113,plain,(
% 1.39/0.53    ( ! [X3] : (~r1_tarski(X3,sK1) | sK2 = sK3 | sK1 = X3) )),
% 1.39/0.53    inference(resolution,[],[f110,f47])).
% 1.39/0.53  fof(f47,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.39/0.53    inference(cnf_transformation,[],[f26])).
% 1.39/0.53  fof(f26,plain,(
% 1.39/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.53    inference(flattening,[],[f25])).
% 1.39/0.53  fof(f25,plain,(
% 1.39/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.53    inference(nnf_transformation,[],[f2])).
% 1.39/0.53  fof(f2,axiom,(
% 1.39/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.53  fof(f110,plain,(
% 1.39/0.53    ( ! [X0] : (r1_tarski(sK1,X0) | sK2 = sK3) )),
% 1.39/0.53    inference(resolution,[],[f109,f49])).
% 1.39/0.53  fof(f49,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f30])).
% 1.39/0.53  fof(f30,plain,(
% 1.39/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.39/0.53  fof(f29,plain,(
% 1.39/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f28,plain,(
% 1.39/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.53    inference(rectify,[],[f27])).
% 1.39/0.53  fof(f27,plain,(
% 1.39/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.53    inference(nnf_transformation,[],[f16])).
% 1.39/0.53  fof(f16,plain,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f1])).
% 1.39/0.53  fof(f1,axiom,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.53  fof(f109,plain,(
% 1.39/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | sK2 = sK3) )),
% 1.39/0.53    inference(resolution,[],[f108,f57])).
% 1.39/0.53  fof(f57,plain,(
% 1.39/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.53    inference(equality_resolution,[],[f46])).
% 1.39/0.53  fof(f46,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.53    inference(cnf_transformation,[],[f26])).
% 1.39/0.53  fof(f108,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | ~r2_hidden(X0,X1) | sK2 = sK3) )),
% 1.39/0.53    inference(resolution,[],[f107,f52])).
% 1.39/0.53  fof(f52,plain,(
% 1.39/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f31])).
% 1.39/0.53  fof(f31,plain,(
% 1.39/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.53    inference(nnf_transformation,[],[f3])).
% 1.39/0.53  fof(f3,axiom,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.53  fof(f107,plain,(
% 1.39/0.53    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | sK2 = sK3 | ~r2_hidden(X3,X2)) )),
% 1.39/0.53    inference(resolution,[],[f105,f54])).
% 1.39/0.53  fof(f54,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f19])).
% 1.39/0.53  fof(f19,plain,(
% 1.39/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.39/0.53    inference(ennf_transformation,[],[f4])).
% 1.39/0.53  fof(f4,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.39/0.53  fof(f105,plain,(
% 1.39/0.53    v1_xboole_0(sK1) | sK2 = sK3),
% 1.39/0.53    inference(subsumption_resolution,[],[f103,f35])).
% 1.39/0.53  fof(f35,plain,(
% 1.39/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.53  fof(f24,plain,(
% 1.39/0.53    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23,f22])).
% 1.39/0.53  % (4653)Refutation not found, incomplete strategy% (4653)------------------------------
% 1.39/0.53  % (4653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.53  % (4653)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.53  
% 1.39/0.53  % (4653)Memory used [KB]: 10746
% 1.39/0.53  % (4653)Time elapsed: 0.124 s
% 1.39/0.53  % (4653)------------------------------
% 1.39/0.53  % (4653)------------------------------
% 1.39/0.53  fof(f22,plain,(
% 1.39/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  % (4655)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.53  fof(f23,plain,(
% 1.39/0.53    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f12,plain,(
% 1.39/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.53    inference(flattening,[],[f11])).
% 1.39/0.53  fof(f11,plain,(
% 1.39/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.53    inference(ennf_transformation,[],[f10])).
% 1.39/0.53  fof(f10,negated_conjecture,(
% 1.39/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.39/0.53    inference(negated_conjecture,[],[f9])).
% 1.39/0.53  fof(f9,conjecture,(
% 1.39/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 1.39/0.53  fof(f103,plain,(
% 1.39/0.53    sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.39/0.53    inference(resolution,[],[f102,f38])).
% 1.39/0.53  fof(f38,plain,(
% 1.39/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.53  fof(f102,plain,(
% 1.39/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(sK1)) )),
% 1.39/0.53    inference(subsumption_resolution,[],[f101,f95])).
% 1.39/0.53  fof(f95,plain,(
% 1.39/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 1.39/0.53    inference(subsumption_resolution,[],[f94,f35])).
% 1.39/0.53  fof(f94,plain,(
% 1.39/0.53    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.39/0.53    inference(resolution,[],[f92,f34])).
% 1.39/0.53  fof(f34,plain,(
% 1.39/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.53  fof(f92,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.39/0.53    inference(resolution,[],[f43,f33])).
% 1.39/0.53  fof(f33,plain,(
% 1.39/0.53    v1_funct_1(sK2)),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.53  fof(f43,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f14])).
% 1.39/0.53  fof(f14,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.39/0.53    inference(flattening,[],[f13])).
% 1.39/0.53  fof(f13,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.39/0.53    inference(ennf_transformation,[],[f7])).
% 1.39/0.53  fof(f7,axiom,(
% 1.39/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.39/0.53  fof(f101,plain,(
% 1.39/0.53    ( ! [X0] : (sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(sK1)) )),
% 1.39/0.53    inference(resolution,[],[f100,f97])).
% 1.39/0.53  fof(f97,plain,(
% 1.39/0.53    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 1.39/0.53    inference(subsumption_resolution,[],[f96,f38])).
% 1.39/0.53  fof(f96,plain,(
% 1.39/0.53    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1)),
% 1.39/0.53    inference(resolution,[],[f93,f37])).
% 1.39/0.53  fof(f37,plain,(
% 1.39/0.53    v1_funct_2(sK3,sK0,sK1)),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.53  fof(f93,plain,(
% 1.39/0.53    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) )),
% 1.39/0.53    inference(resolution,[],[f43,f36])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    v1_funct_1(sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f100,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_partfun1(sK3,X0) | sK2 = sK3 | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f99,f33])).
% 1.39/0.54  fof(f99,plain,(
% 1.39/0.54    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 1.39/0.54    inference(subsumption_resolution,[],[f98,f36])).
% 1.39/0.54  % (4672)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    ( ! [X0,X1] : (sK2 = sK3 | ~v1_partfun1(sK3,X0) | ~v1_partfun1(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK2)) )),
% 1.39/0.54    inference(resolution,[],[f53,f39])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    r1_partfun1(sK2,sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.54    inference(flattening,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    ( ! [X0] : (r1_tarski(sK2,X0) | sK2 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f140,f49])).
% 1.39/0.54  fof(f140,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | sK2 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f139,f57])).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK2) | ~r2_hidden(X0,X1) | sK2 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f129,f52])).
% 1.39/0.54  fof(f129,plain,(
% 1.39/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK2)) | sK2 = sK3 | ~r2_hidden(X3,X2)) )),
% 1.39/0.54    inference(resolution,[],[f125,f54])).
% 1.39/0.54  fof(f125,plain,(
% 1.39/0.54    v1_xboole_0(sK2) | sK2 = sK3),
% 1.39/0.54    inference(resolution,[],[f106,f35])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | sK2 = sK3 | v1_xboole_0(X0)) )),
% 1.39/0.54    inference(resolution,[],[f105,f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f70,plain,(
% 1.39/0.54    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.39/0.54    inference(resolution,[],[f60,f35])).
% 1.39/0.54  fof(f60,plain,(
% 1.39/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f59])).
% 1.39/0.54  fof(f59,plain,(
% 1.39/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(equality_resolution,[],[f56])).
% 1.39/0.54  fof(f56,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.54    inference(cnf_transformation,[],[f32])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(nnf_transformation,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.54    inference(flattening,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.39/0.54    inference(ennf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.39/0.54  fof(f304,plain,(
% 1.39/0.54    ~r2_relset_1(sK0,sK1,sK1,sK1)),
% 1.39/0.54    inference(backward_demodulation,[],[f180,f290])).
% 1.39/0.54  fof(f290,plain,(
% 1.39/0.54    sK1 = sK3),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f282])).
% 1.39/0.54  fof(f282,plain,(
% 1.39/0.54    sK1 = sK3 | sK1 = sK3 | sK1 = sK3),
% 1.39/0.54    inference(resolution,[],[f276,f198])).
% 1.39/0.54  fof(f198,plain,(
% 1.39/0.54    ( ! [X3] : (~r1_tarski(X3,sK1) | sK1 = sK3 | sK1 = X3) )),
% 1.39/0.54    inference(backward_demodulation,[],[f113,f175])).
% 1.39/0.54  fof(f276,plain,(
% 1.39/0.54    ( ! [X0] : (r1_tarski(sK3,X0) | sK1 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f272,f49])).
% 1.39/0.54  fof(f272,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,sK3) | sK1 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f271,f57])).
% 1.39/0.54  fof(f271,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK3) | ~r2_hidden(X0,X1) | sK1 = sK3) )),
% 1.39/0.54    inference(resolution,[],[f206,f52])).
% 1.39/0.54  fof(f206,plain,(
% 1.39/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(sK3)) | sK1 = sK3 | ~r2_hidden(X3,X2)) )),
% 1.39/0.54    inference(backward_demodulation,[],[f131,f175])).
% 1.39/0.54  fof(f131,plain,(
% 1.39/0.54    ( ! [X2,X3] : (sK2 = sK3 | ~m1_subset_1(X2,k1_zfmisc_1(sK3)) | ~r2_hidden(X3,X2)) )),
% 1.39/0.54    inference(resolution,[],[f126,f54])).
% 1.39/0.54  fof(f126,plain,(
% 1.39/0.54    v1_xboole_0(sK3) | sK2 = sK3),
% 1.39/0.54    inference(resolution,[],[f106,f38])).
% 1.39/0.54  fof(f180,plain,(
% 1.39/0.54    ~r2_relset_1(sK0,sK1,sK1,sK3)),
% 1.39/0.54    inference(backward_demodulation,[],[f41,f175])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (4650)------------------------------
% 1.39/0.54  % (4650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (4650)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (4650)Memory used [KB]: 6396
% 1.39/0.54  % (4650)Time elapsed: 0.112 s
% 1.39/0.54  % (4650)------------------------------
% 1.39/0.54  % (4650)------------------------------
% 1.39/0.54  % (4642)Success in time 0.184 s
%------------------------------------------------------------------------------

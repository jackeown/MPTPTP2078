%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:40 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 428 expanded)
%              Number of leaves         :   17 ( 132 expanded)
%              Depth                    :   23
%              Number of atoms          :  388 (3053 expanded)
%              Number of equality atoms :   55 (  93 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(subsumption_resolution,[],[f363,f175])).

fof(f175,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f50,f153])).

fof(f153,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f140,f53])).

% (26208)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f140,plain,(
    v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f54,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f363,plain,(
    ~ v2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f138,f351])).

fof(f351,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f283,f53])).

fof(f283,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f228,f49])).

fof(f228,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(backward_demodulation,[],[f81,f221])).

fof(f221,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f220,f138])).

% (26215)Refutation not found, incomplete strategy% (26215)------------------------------
% (26215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26215)Termination reason: Refutation not found, incomplete strategy

% (26215)Memory used [KB]: 10874
% (26215)Time elapsed: 0.120 s
% (26215)------------------------------
% (26215)------------------------------
fof(f220,plain,
    ( v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f211,f50])).

fof(f211,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f121,f204])).

fof(f204,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(resolution,[],[f162,f91])).

fof(f91,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f90,f72])).

fof(f90,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f47,f51])).

fof(f47,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f162,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f149,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f124,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f95,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f121,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f101,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(X3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(X3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f81,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f54,f43])).

fof(f138,plain,(
    ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f133,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(subsumption_resolution,[],[f132,f76])).

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f132,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f131,f79])).

fof(f79,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f131,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f67,f130])).

fof(f130,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f88,f129])).

fof(f129,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f127,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f71])).

fof(f126,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f105,f45])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK1,sK0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f104,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f102,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f73,f42])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f88,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (26228)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (26220)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (26210)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (26209)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (26212)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (26214)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (26211)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26215)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (26228)Refutation not found, incomplete strategy% (26228)------------------------------
% 0.22/0.53  % (26228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26228)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26228)Memory used [KB]: 10874
% 0.22/0.53  % (26228)Time elapsed: 0.070 s
% 0.22/0.53  % (26228)------------------------------
% 0.22/0.53  % (26228)------------------------------
% 0.22/0.53  % (26224)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (26229)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (26205)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (26207)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.42/0.54  % (26232)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.54  % (26212)Refutation found. Thanks to Tanya!
% 1.42/0.54  % SZS status Theorem for theBenchmark
% 1.42/0.54  % SZS output start Proof for theBenchmark
% 1.42/0.54  fof(f421,plain,(
% 1.42/0.54    $false),
% 1.42/0.54    inference(subsumption_resolution,[],[f363,f175])).
% 1.42/0.54  fof(f175,plain,(
% 1.42/0.54    v2_funct_1(k1_xboole_0)),
% 1.42/0.54    inference(superposition,[],[f50,f153])).
% 1.42/0.54  fof(f153,plain,(
% 1.42/0.54    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.42/0.54    inference(resolution,[],[f140,f53])).
% 1.42/0.54  % (26208)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.54  fof(f53,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f21])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.42/0.54  fof(f140,plain,(
% 1.42/0.54    v1_xboole_0(k6_relat_1(k1_xboole_0))),
% 1.42/0.54    inference(resolution,[],[f83,f49])).
% 1.42/0.54  fof(f49,plain,(
% 1.42/0.54    v1_xboole_0(k1_xboole_0)),
% 1.42/0.54    inference(cnf_transformation,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    v1_xboole_0(k1_xboole_0)),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.42/0.54  fof(f83,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k6_relat_1(X0))) )),
% 1.42/0.54    inference(resolution,[],[f54,f72])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.54    inference(forward_demodulation,[],[f52,f51])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f12])).
% 1.42/0.54  fof(f12,axiom,(
% 1.42/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f17])).
% 1.42/0.54  fof(f17,plain,(
% 1.42/0.54    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.42/0.54    inference(pure_predicate_removal,[],[f11])).
% 1.42/0.54  fof(f11,axiom,(
% 1.42/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.42/0.54  fof(f54,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f22])).
% 1.42/0.54  fof(f22,plain,(
% 1.42/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.42/0.54  fof(f50,plain,(
% 1.42/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.42/0.54  fof(f363,plain,(
% 1.42/0.54    ~v2_funct_1(k1_xboole_0)),
% 1.42/0.54    inference(backward_demodulation,[],[f138,f351])).
% 1.42/0.54  fof(f351,plain,(
% 1.42/0.54    k1_xboole_0 = sK2),
% 1.42/0.54    inference(resolution,[],[f283,f53])).
% 1.42/0.54  fof(f283,plain,(
% 1.42/0.54    v1_xboole_0(sK2)),
% 1.42/0.54    inference(subsumption_resolution,[],[f228,f49])).
% 1.42/0.54  fof(f228,plain,(
% 1.42/0.54    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 1.42/0.54    inference(backward_demodulation,[],[f81,f221])).
% 1.42/0.54  fof(f221,plain,(
% 1.42/0.54    k1_xboole_0 = sK0),
% 1.42/0.54    inference(subsumption_resolution,[],[f220,f138])).
% 1.42/0.54  % (26215)Refutation not found, incomplete strategy% (26215)------------------------------
% 1.42/0.54  % (26215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (26215)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (26215)Memory used [KB]: 10874
% 1.42/0.54  % (26215)Time elapsed: 0.120 s
% 1.42/0.54  % (26215)------------------------------
% 1.42/0.54  % (26215)------------------------------
% 1.42/0.54  fof(f220,plain,(
% 1.42/0.54    v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 1.42/0.54    inference(subsumption_resolution,[],[f211,f50])).
% 1.42/0.54  fof(f211,plain,(
% 1.42/0.54    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 1.42/0.54    inference(backward_demodulation,[],[f121,f204])).
% 1.42/0.54  fof(f204,plain,(
% 1.42/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.42/0.54    inference(resolution,[],[f162,f91])).
% 1.42/0.54  fof(f91,plain,(
% 1.42/0.54    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.42/0.54    inference(subsumption_resolution,[],[f90,f72])).
% 1.42/0.54  fof(f90,plain,(
% 1.42/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.54    inference(resolution,[],[f63,f71])).
% 1.42/0.54  fof(f71,plain,(
% 1.42/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.42/0.54    inference(forward_demodulation,[],[f47,f51])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f38,plain,(
% 1.42/0.54    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f37,f36])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f37,plain,(
% 1.42/0.54    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.54    inference(flattening,[],[f19])).
% 1.42/0.54  fof(f19,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.54    inference(ennf_transformation,[],[f16])).
% 1.42/0.54  fof(f16,negated_conjecture,(
% 1.42/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.54    inference(negated_conjecture,[],[f15])).
% 1.42/0.54  fof(f15,conjecture,(
% 1.42/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f40])).
% 1.42/0.54  fof(f40,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    inference(nnf_transformation,[],[f33])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    inference(flattening,[],[f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.42/0.54    inference(ennf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.42/0.54  fof(f162,plain,(
% 1.42/0.54    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.54    inference(resolution,[],[f149,f46])).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f149,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.42/0.54    inference(resolution,[],[f124,f43])).
% 1.42/0.54  fof(f43,plain,(
% 1.42/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f124,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.42/0.54    inference(resolution,[],[f95,f41])).
% 1.42/0.54  fof(f41,plain,(
% 1.42/0.54    v1_funct_1(sK2)),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f95,plain,(
% 1.42/0.54    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.42/0.54    inference(resolution,[],[f66,f44])).
% 1.42/0.54  fof(f44,plain,(
% 1.42/0.54    v1_funct_1(sK3)),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f66,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f35])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.54    inference(flattening,[],[f34])).
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.42/0.54  fof(f121,plain,(
% 1.42/0.54    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | k1_xboole_0 = sK0),
% 1.42/0.54    inference(subsumption_resolution,[],[f120,f41])).
% 1.42/0.54  fof(f120,plain,(
% 1.42/0.54    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 1.42/0.54    inference(subsumption_resolution,[],[f119,f43])).
% 1.42/0.54  fof(f119,plain,(
% 1.42/0.54    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2)),
% 1.42/0.54    inference(resolution,[],[f101,f42])).
% 1.42/0.54  fof(f42,plain,(
% 1.42/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f101,plain,(
% 1.42/0.54    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | k1_xboole_0 = sK0 | ~v1_funct_1(X3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f100,f44])).
% 1.42/0.54  fof(f100,plain,(
% 1.42/0.54    ( ! [X2,X3] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(X3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f97,f46])).
% 1.42/0.54  fof(f97,plain,(
% 1.42/0.54    ( ! [X2,X3] : (k1_xboole_0 = sK0 | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(X3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 1.42/0.54    inference(resolution,[],[f61,f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f31])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.42/0.54    inference(flattening,[],[f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.42/0.54    inference(ennf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,axiom,(
% 1.42/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.42/0.54  fof(f81,plain,(
% 1.42/0.54    ~v1_xboole_0(sK0) | v1_xboole_0(sK2)),
% 1.42/0.54    inference(resolution,[],[f54,f43])).
% 1.42/0.54  fof(f138,plain,(
% 1.42/0.54    ~v2_funct_1(sK2)),
% 1.42/0.54    inference(resolution,[],[f133,f48])).
% 1.42/0.54  fof(f48,plain,(
% 1.42/0.54    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.42/0.54    inference(cnf_transformation,[],[f38])).
% 1.42/0.54  fof(f133,plain,(
% 1.42/0.54    v2_funct_2(sK3,sK0)),
% 1.42/0.54    inference(subsumption_resolution,[],[f132,f76])).
% 1.42/0.54  fof(f76,plain,(
% 1.42/0.54    v1_relat_1(sK3)),
% 1.42/0.54    inference(resolution,[],[f57,f46])).
% 1.42/0.54  fof(f57,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f25])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    inference(ennf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.54  fof(f132,plain,(
% 1.42/0.54    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f131,f79])).
% 1.42/0.54  fof(f79,plain,(
% 1.42/0.54    v5_relat_1(sK3,sK0)),
% 1.42/0.54    inference(resolution,[],[f59,f46])).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f27])).
% 1.42/0.54  fof(f27,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    inference(ennf_transformation,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.42/0.54    inference(pure_predicate_removal,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.42/0.54  fof(f131,plain,(
% 1.42/0.54    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.42/0.54    inference(superposition,[],[f67,f130])).
% 1.42/0.54  fof(f130,plain,(
% 1.42/0.54    sK0 = k2_relat_1(sK3)),
% 1.42/0.54    inference(backward_demodulation,[],[f88,f129])).
% 1.42/0.54  fof(f129,plain,(
% 1.42/0.54    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f128,f44])).
% 1.42/0.54  fof(f128,plain,(
% 1.42/0.54    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f127,f46])).
% 1.42/0.54  fof(f127,plain,(
% 1.42/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f126,f71])).
% 1.42/0.54  fof(f126,plain,(
% 1.42/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.42/0.54    inference(resolution,[],[f105,f45])).
% 1.42/0.54  fof(f105,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_funct_2(X0,sK1,sK0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(X0)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f104,f41])).
% 1.42/0.54  fof(f104,plain,(
% 1.42/0.54    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f102,f43])).
% 1.42/0.54  fof(f102,plain,(
% 1.42/0.54    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.42/0.54    inference(resolution,[],[f73,f42])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/0.54    inference(forward_demodulation,[],[f60,f51])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/0.54    inference(flattening,[],[f28])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/0.54    inference(ennf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.42/0.54  fof(f88,plain,(
% 1.42/0.54    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.42/0.54    inference(resolution,[],[f58,f46])).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.42/0.54  fof(f67,plain,(
% 1.42/0.54    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.42/0.54    inference(equality_resolution,[],[f56])).
% 1.42/0.54  fof(f56,plain,(
% 1.42/0.54    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f39])).
% 1.42/0.54  fof(f39,plain,(
% 1.42/0.54    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.54    inference(nnf_transformation,[],[f24])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.54    inference(flattening,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.42/0.54    inference(ennf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (26212)------------------------------
% 1.42/0.54  % (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (26212)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (26212)Memory used [KB]: 2046
% 1.42/0.54  % (26212)Time elapsed: 0.087 s
% 1.42/0.54  % (26212)------------------------------
% 1.42/0.54  % (26212)------------------------------
% 1.42/0.55  % (26204)Success in time 0.183 s
%------------------------------------------------------------------------------
